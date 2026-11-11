import random
import time

class QuineMcCluskey:
    """Quine-McCluskey Boolean minimizer for transition event/guard expressions."""
    @staticmethod
    def minimize(minterms, num_vars):
        if not minterms:
            return set()
        if len(set(minterms)) == (1 << num_vars):
            return {"TRUE"}

        groups = {}
        for m in set(minterms):
            bin_str = format(m, f'0{num_vars}b')
            ones = bin_str.count('1')
            groups.setdefault(ones, set()).add(bin_str)

        prime_implicants = set()
        while groups:
            next_groups = {}
            used = set()
            sorted_keys = sorted(groups.keys())
            for i in range(len(sorted_keys) - 1):
                k1, k2 = sorted_keys[i], sorted_keys[i + 1]
                if k2 - k1 == 1:
                    for a in groups[k1]:
                        for b in groups[k2]:
                            diff = [idx for idx in range(num_vars) if a[idx] != b[idx]]
                            if len(diff) == 1:
                                used.add(a)
                                used.add(b)
                                pos = diff[0]
                                merged = a[:pos] + '-' + a[pos + 1:]
                                next_groups.setdefault(merged.count('1'), set()).add(merged)
            for g in groups.values():
                for term in g:
                    if term not in used:
                        prime_implicants.add(term)
            groups = next_groups
        return prime_implicants


class StatechartModel:
    """Formal UML Statechart G(V, E) with composite superstate support."""
    def __init__(self, states, initial_state, composite_states=None):
        self.states = set(states)
        self.initial_state = initial_state
        self.composite_states = composite_states or {}
        self.transitions = {}

    def add_transition(self, src, dst, minterms):
        self.transitions.setdefault((src, dst), []).extend(minterms)

    def edge_count(self):
        return len(self.transitions)

    def get_reachable_states(self):
        """Prunes disconnected/dead states via DFS reachability."""
        visited = set()
        stack = [self.initial_state]
        while stack:
            curr = stack.pop()
            if curr not in visited:
                visited.add(curr)
                if curr in self.composite_states:
                    stack.extend(self.composite_states[curr])
                for (src, dst) in self.transitions:
                    if src == curr and dst not in visited:
                        stack.append(dst)
        return visited

    def build_flattened_matrix(self, num_vars=4):
        """Flattens composite transitions and minimizes guards via Quine-McCluskey."""
        reachable = self.get_reachable_states()
        atomic_states = sorted([s for s in reachable if s not in self.composite_states])
        raw_matrix = {(u, v): [] for u in atomic_states for v in atomic_states}

        for (src, dst), minterms in self.transitions.items():
            sources = self.composite_states[src] if src in self.composite_states else [src]
            for s in sources:
                if s in atomic_states and dst in atomic_states:
                    raw_matrix[(s, dst)].extend(minterms)

        minimized_matrix = {}
        for pair, minterms in raw_matrix.items():
            minimized_matrix[pair] = QuineMcCluskey.minimize(minterms, num_vars)
        return atomic_states, minimized_matrix


def verify_refactoring(pre_model, post_model, num_vars=4):
    """Computes Delta-M between pre- and post-refactoring statecharts."""
    start_time = time.perf_counter()
    states_pre, mat_pre = pre_model.build_flattened_matrix(num_vars)
    states_post, mat_post = post_model.build_flattened_matrix(num_vars)

    if states_pre != states_post:
        elapsed_ms = (time.perf_counter() - start_time) * 1000
        return False, {"state_mismatch": len(set(states_pre) ^ set(states_post))}, elapsed_ms

    deltas = {}
    for u in states_pre:
        for v in states_pre:
            if mat_pre[(u, v)] != mat_post[(u, v)]:
                deltas[(u, v)] = (mat_pre[(u, v)], mat_post[(u, v)])

    elapsed_ms = (time.perf_counter() - start_time) * 1000
    return (len(deltas) == 0), deltas, elapsed_ms


def generate_benchmark_pair(num_states, seed, inject_fault=False):
    """Generates a realistic pre- and post-refactored statechart pair."""
    rng = random.Random(seed)
    states = [f"S{i}" for i in range(num_states)]
    root = states[0]
    cluster_size = max(3, num_states // 3)
    cluster = states[1 : 1 + cluster_size]
    other_states = states[1 + cluster_size :]

    pre = StatechartModel(states, initial_state=root)
    post = StatechartModel(
        states + ["Composite_C1"],
        initial_state=root,
        composite_states={"Composite_C1": cluster}
    )

    # Ensure full reachability backbone
    for i in range(num_states - 1):
        m = [rng.randint(0, 14)]
        pre.add_transition(states[i], states[i + 1], m)
        post.add_transition(states[i], states[i + 1], list(m))

    # Add internal cross-transitions
    for _ in range(num_states):
        u, v = rng.choice(states), rng.choice(states)
        if u != v and v != root:
            m = [rng.randint(0, 14)]
            pre.add_transition(u, v, m)
            post.add_transition(u, v, list(m))

    # High-coupling pattern: every state in cluster transitions to root on event 15
    shared_event = [15]
    for s in cluster:
        pre.add_transition(s, root, shared_event)

    # Refactored model replaces all individual cluster->root edges with 1 composite edge
    post.add_transition("Composite_C1", root, shared_event)

    # Inject a "bad fix" mutation if testing fault detection
    if inject_fault:
        fault_type = seed % 3
        if fault_type == 0 and other_states:
            # Mutation 1: Missing transition during refactoring
            target = other_states[0]
            post.transitions.pop((states[-2], target), None)
            if (states[-2], states[-1]) in post.transitions:
                del post.transitions[(states[-2], states[-1])]
        elif fault_type == 1:
            # Mutation 2: Guard corruption (altered minterm)
            post.add_transition(cluster[0], cluster[-1], [14])
        else:
            # Mutation 3: Misrouted composite transition
            wrong_target = other_states[0] if other_states else cluster[0]
            del post.transitions[("Composite_C1", root)]
            post.add_transition("Composite_C1", wrong_target, shared_event)

    return pre, post


def run_benchmark():
    tiers = [
        ("Small (10 states)", 10, 5),
        ("Medium (25 states)", 25, 5),
        ("Large (50 states)", 50, 5),
        ("X-Large (100 states)", 100, 5),
        ("Enterprise (200 states)", 200, 5),
    ]

    tp = tn = fp = fn = 0
    latex_rows = []
    seed_counter = 100

    print(f"{'Tier':<24} | {'Models':<6} | {'Pre-Edges':<9} | {'Post-Edges':<10} | {'Acc (%)':<7} | {'Avg Time (ms)':<13}")
    print("-" * 82)

    for tier_name, n_states, count in tiers:
        tier_pre_edges = []
        tier_post_edges = []
        tier_times = []
        tier_correct = 0
        tier_total = count * 2  # 1 valid + 1 faulty per model

        for _ in range(count):
            seed_counter += 1
            # 1. Valid Refactoring Test (Expected: Equivalent = True)
            pre_v, post_v = generate_benchmark_pair(n_states, seed_counter, inject_fault=False)
            is_eq_v, _, t_v = verify_refactoring(pre_v, post_v)
            tier_pre_edges.append(pre_v.edge_count())
            tier_post_edges.append(post_v.edge_count())
            tier_times.append(t_v)
            if is_eq_v:
                tn += 1
                tier_correct += 1
            else:
                fp += 1

            # 2. Faulty Refactoring Test (Expected: Equivalent = False)
            pre_f, post_f = generate_benchmark_pair(n_states, seed_counter, inject_fault=True)
            is_eq_f, _, t_f = verify_refactoring(pre_f, post_f)
            tier_times.append(t_f)
            if not is_eq_f:
                tp += 1
                tier_correct += 1
            else:
                fn += 1

        avg_pre = sum(tier_pre_edges) / count
        avg_post = sum(tier_post_edges) / count
        coupling_red = ((avg_pre - avg_post) / avg_pre) * 100
        avg_ms = sum(tier_times) / len(tier_times)
        acc = (tier_correct / tier_total) * 100

        print(f"{tier_name:<24} | {count:<6} | {avg_pre:<9.1f} | {avg_post:<10.1f} | {acc:<7.1f} | {avg_ms:<13.3f}")
        latex_rows.append(
            f"{tier_name} & {count} & {avg_pre:.1f} & {avg_post:.1f} (-{coupling_red:.1f}\\%) & {acc:.1f}\\% & {avg_ms:.2f} \\\\"
        )

    precision = (tp / (tp + fp)) * 100 if (tp + fp) else 0
    recall = (tp / (tp + fn)) * 100 if (tp + fn) else 0
    print("-" * 82)
    print(f"Overall Summary (25 Models / 50 Refactoring Runs): Precision={precision:.1f}%, Recall={recall:.1f}%\n")

    print("=== READY-TO-PASTE LATEX TABLE FOR SECTION 4 ===")
    print(r"\begin{table}[htbp]")
    print(r"\centering")
    print(r"\caption{Empirical Evaluation Across 25 Statechart Models (Valid vs. Fault-Injected Refactorings)}")
    print(r"\label{tab:benchmark_results}")
    print(r"\begin{tabular}{lccccc}")
    print(r"\hline")
    print(r"\textbf{Model Scale} & \textbf{Models} & \textbf{Pre-Edges} & \textbf{Post-Edges} & \textbf{Accuracy} & \textbf{Time (ms)} \\")
    print(r"\hline")
    for row in latex_rows:
        print(row)
    print(r"\hline")
    print(r"\end{tabular}")
    print(r"\end{table}")


if __name__ == "__main__":
    run_benchmark()
