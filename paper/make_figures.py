"""Illustrative trajectories for the three-species example (Figure 2 of the paper).

Declared schedules only; no simulation is theorem evidence.  Run from the
repository root with Python, NumPy, SciPy and Matplotlib:

    python paper/make_figures.py

Writes figures/operating_trajectories.pdf (vector, used by main.tex),
figures/operating_trajectories.png and figures/trajectory_data.json next to
this script.  The script asserts that every sampled state after the proved
staged deadline 347/16 lies in the operating box [0.4, 2.5]^3; this is a
consistency check of the illustration against the theorem, not evidence.
"""
import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

here = Path(__file__).resolve().parent
out = here / "figures"
out.mkdir(parents=True, exist_ok=True)
DEADLINE = 347 / 16
starts = [[.1, .1, .1], [10, 10, 10], [.1, 10, .1], [10, .1, 10]]
styles = ["-", "--", ":", "-."]
time = np.linspace(0, 40, 1601)


def rates(t, schedule):
    if schedule == "constant":
        return np.array([.5, 2, .5, 2, .5, 2])
    if schedule == "periodic":
        return 1.25 + .75 * np.sin(2 * np.pi * t / 8 + np.arange(6) * np.pi / 3)
    # piecewise constant; segments are integrated separately at the exact jumps
    j = int(np.floor(t / 2))
    return np.array([.5 if (j + i) % 3 == 0 else 2 for i in range(6)])


def field(k, x):
    a, b, c = x
    return [c * (k[0] - k[1] * a * a), a * b * (k[2] - k[3] * b * b), b * c * (k[4] - k[5] * c * c)]


data = {}
fig, axes = plt.subplots(1, 3, figsize=(10.8, 3.6), sharex=True, sharey=True)
colors = ["#2166ac", "#d6604d", "#1b7837"]
for ax, schedule in zip(axes, ["constant", "periodic", "switching"]):
    for index, start in enumerate(starts):
        if schedule == "switching":
            values = []
            state = np.array(start, dtype=float)
            for left in np.arange(0, 40, 2):
                right = left + 2
                frozen = rates(left + .1, schedule)
                sol = solve_ivp(lambda t, x: field(frozen, x), (left, right), state, method="LSODA",
                                rtol=1e-9, atol=1e-11, dense_output=True)
                assert sol.success
                selected = time[(time >= left) & (time < right)]
                values.append(sol.sol(selected))
                state = sol.y[:, -1]
            values.append(state[:, None])
            values = np.concatenate(values, axis=1)
        else:
            sol = solve_ivp(lambda t, x: field(rates(t, schedule), x), (0, 40), start, method="LSODA",
                            rtol=1e-9, atol=1e-11, t_eval=time)
            assert sol.success
            values = sol.y
        assert values.shape == (3, len(time))
        assert np.min(values) > 0
        assert np.min(values[:, time >= DEADLINE]) >= .4 - 1e-7, (schedule, start)
        assert np.max(values[:, time >= DEADLINE]) <= 2.5 + 1e-7, (schedule, start)
        data[f"{schedule}_{index}"] = {"initial": start, "values": values.tolist()}
        for i in range(3):
            ax.plot(time, values[i], color=colors[i], ls=styles[index], lw=.9, alpha=.75,
                    label="abc"[i] if index == 0 else None)
    ax.axhspan(.4, 2.5, color="#e6efdf", zorder=-2)
    ax.axvline(DEADLINE, color="#333333", ls="--", lw=1)
    ax.axhline(.4, color="#677962", lw=.5)
    ax.axhline(2.5, color="#677962", lw=.5)
    ax.set_yscale("log")
    ax.set_ylim(.085, 12)
    ax.set_xlim(0, 40)
    ax.set_title(schedule.capitalize(), fontsize=13)
    ax.set_xlabel("Nondimensional time", fontsize=11)
    ax.tick_params(labelsize=10)
axes[0].set_ylabel("Concentration (log scale)", fontsize=11)
axes[0].legend(frameon=False, ncol=3, fontsize=10, loc="upper right", columnspacing=.8)
fig.tight_layout(pad=.7, w_pad=1.5)
fig.savefig(out / "operating_trajectories.pdf")
fig.savefig(out / "operating_trajectories.png", dpi=200)
plt.close(fig)
payload = {"time": time.tolist(), "trajectories": data, "deadline": DEADLINE,
           "line_styles": dict(zip(["solid", "dashed", "dotted", "dashdot"], [list(s) for s in starts])),
           "rate_schedules": {"constant": "(.5,2,.5,2,.5,2)",
                              "periodic": "1.25+.75 sin(2 pi t/8+(i-1) pi/3)",
                              "switching": ".5 if (floor(t/2)+(i-1)) mod 3 = 0; otherwise 2"},
           "solver": {"method": "LSODA", "rtol": 1e-9, "atol": 1e-11},
           "interpretation": "Illustrations only; the all-history guarantee follows from the proof."}
(out / "trajectory_data.json").write_text(json.dumps(payload) + "\n")
print(json.dumps({"trajectories": len(data), "samples_each": len(time), "deadline": DEADLINE,
                  "figure": str(out / "operating_trajectories.pdf")}, indent=2))
