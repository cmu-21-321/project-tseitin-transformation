"""Monte Carlo comparison with the exact shared-supply failure probability.
This empirical Python experiment is separate from the Lean proofs.
"""

import csv
import itertools
import json
import math
import random
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results"

PROBABILITIES = (
    Fraction(1, 100),
    Fraction(1, 10),
    Fraction(1, 10),
)
SAMPLE_SIZES = (1000, 10000, 100000)
REPETITIONS = 100


def fails(a, b, c):
    return (a or b) and (a or c)


def exact_probability():
    """Enumerate all eight basic-event states using exact fractions."""
    total = Fraction(0)

    for state in itertools.product((False, True), repeat=3):
        if fails(*state):
            total += math.prod(
                p if value else 1 - p
                for p, value in zip(PROBABILITIES, state)
            )

    return total


def wilson_interval(successes, n):
    """Two-sided nominal 95% Wilson score interval."""
    z = 1.959963984540054
    estimate = successes / n
    denominator = 1 + z * z / n
    center = (estimate + z * z / (2 * n)) / denominator
    half = z * math.sqrt(
        estimate * (1 - estimate) / n
        + z * z / (4 * n * n)
    ) / denominator

    return center - half, center + half


def save_csv(name, rows):
    with (OUT / name).open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0])
        )
        writer.writeheader()
        writer.writerows(rows)


def main():
    OUT.mkdir(parents=True, exist_ok=True)

    exact = exact_probability()
    if exact != Fraction(199, 10000):
        raise RuntimeError(
            "Reference calculation disagrees with the Lean result"
        )

    truth = float(exact)
    raw, summary = [], []

    print(
        f"Exact failure probability: {exact}"
        f" = {100 * truth:.4f}%"
    )
    print("N | mean (%) | MAE (pp) | RMSE (pp) | coverage")

    for n in SAMPLE_SIZES:
        estimates, covered_count = [], 0

        for repetition in range(REPETITIONS):
            seed = 20261111 + n * 1000 + repetition
            rng = random.Random(seed)
            failures = 0

            for _ in range(n):
                # Draw A once per system state:
                # both branches share the same supply event.
                a = rng.randrange(100) == 0
                b = rng.randrange(10) == 0
                c = rng.randrange(10) == 0
                failures += fails(a, b, c)

            estimate = failures / n
            lo, hi = wilson_interval(failures, n)
            covered = lo <= truth <= hi

            estimates.append(estimate)
            covered_count += int(covered)

            raw.append(dict(
                samples=n,
                repetition=repetition,
                seed=seed,
                failures=failures,
                estimate=estimate,
                exact=truth,
                absolute_error=abs(estimate - truth),
                wilson_lower=lo,
                wilson_upper=hi,
                covered=int(covered),
            ))

        mean = sum(estimates) / REPETITIONS

        mae = sum(
            abs(x - truth) for x in estimates
        ) / REPETITIONS

        rmse = math.sqrt(
            sum((x - truth) ** 2 for x in estimates)
            / REPETITIONS
        )

        summary.append(dict(
            samples=n,
            repetitions=REPETITIONS,
            mean_estimate=mean,
            mae=mae,
            rmse=rmse,
            theoretical_rmse=math.sqrt(
                truth * (1 - truth) / n
            ),
            wilson_coverage=covered_count / REPETITIONS,
        ))

        print(
            f"{n:,} | {100 * mean:.4f} | "
            f"{100 * mae:.4f} | {100 * rmse:.4f} | "
            f"{covered_count}/{REPETITIONS}"
        )

    save_csv("monte_carlo_raw.csv", raw)
    save_csv("monte_carlo_summary.csv", summary)

    metadata = dict(
        python=sys.version,
        exact=str(exact),
        basic_probabilities=list(map(str, PROBABILITIES)),
        sample_sizes=SAMPLE_SIZES,
        repetitions=REPETITIONS,
        seed_rule="20261111 + sample_count * 1000 + repetition",
        interval="Wilson two-sided nominal 95%",
        verified_in_lean=False,
    )

    (OUT / "experiment_metadata.json").write_text(
        json.dumps(metadata, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"Saved {len(raw)} runs to {OUT}")


if __name__ == "__main__":
    main()