#!/usr/bin/env python3
"""fig-profile.png -- what the self-decomposability condition means for the profile.

Left: a nonincreasing displacement profile k, its two dilates k(x/s) and k(x/t) for s < t, and
their difference k(x/t) - k(x/s), which is the profile of the increment from s to t (Lemma 7.1
of the paper, the dilation identity). The difference is nonnegative exactly because k is
nonincreasing and x/t < x/s. Right: the same in the log-displacement coordinate theta = log x,
where dilation is translation and the increment profile is the difference of two translates.

The profile drawn is the Matern member's, k(x) = 2 gamma e^{-x} with gamma = 1, at s = 1 and
t = 2; the picture is the same for any nonincreasing k. numpy and matplotlib only.

Run:  python scripts/make-fig-profile.py      Out:  figures/fig-profile.png
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures", "fig-profile.png")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
plt.rcParams.update({"font.size": 9.5, "axes.linewidth": 0.8})

gamma, s, t = 1.0, 1.0, 2.0


def k(x):
    return 2 * gamma * np.exp(-x)


fig, (axl, axr) = plt.subplots(1, 2, figsize=(8.6, 3.2))

x = np.linspace(0.0, 8.0, 800)
ks, kt = k(x / s), k(x / t)
axl.plot(x, ks, color="#6a4c93", lw=1.6, label=r"$k(x/s)$, $s=1$")
axl.plot(x, kt, color="#1b6ca8", lw=1.6, label=r"$k(x/t)$, $t=2$")
axl.fill_between(x, ks, kt, color="#2a9d8f", alpha=0.25, lw=0)
axl.plot(x, kt - ks, color="#2a9d8f", lw=1.6, ls="--", label=r"$k(x/t)-k(x/s)\geq 0$")
axl.set_xlim(0, 8); axl.set_ylim(0, 2.1)
axl.set_xlabel(r"$x$"); axl.set_ylabel("profile")
axl.set_title("the increment profile is a difference of dilates", fontsize=9.5)
axl.legend(fontsize=7.5, frameon=False)

theta = np.linspace(-3.0, 3.0, 800)
kts, ktt = k(np.exp(theta) / s), k(np.exp(theta) / t)
axr.plot(theta, kts, color="#6a4c93", lw=1.6, label=r"$\tilde k(\theta - \log s)$")
axr.plot(theta, ktt, color="#1b6ca8", lw=1.6, label=r"$\tilde k(\theta - \log t)$")
axr.fill_between(theta, kts, ktt, color="#2a9d8f", alpha=0.25, lw=0)
axr.annotate("", xy=(np.log(t) + 0.3, 1.0), xytext=(0.3, 1.0),
             arrowprops=dict(arrowstyle="->", color="#555555", lw=1.0))
axr.text(0.45, 1.08, r"shift by $\log(t/s)$", fontsize=8, color="#555555")
axr.set_xlim(-3, 3); axr.set_ylim(0, 2.1)
axr.set_xlabel(r"$\theta = \log x$")
axr.set_title("in log-displacement, dilation is translation", fontsize=9.5)
axr.legend(fontsize=7.5, frameon=False, loc="upper right")
for ax in (axl, axr):
    for sp in ("top", "right"):
        ax.spines[sp].set_visible(False)
fig.tight_layout()
fig.savefig(OUT, dpi=200)
print("wrote", OUT)
