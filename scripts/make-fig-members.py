#!/usr/bin/env python3
"""fig-members.png -- the two members of the paper's section 3 at unit canonical scale.

Left: the Matern kernels with transform (1 + omega^2)^(-gamma), gamma = 1/2, 1, 2, 4, on a linear
scale, with the Gaussian of variance 2*gamma at gamma = 2 for contrast (the variance the Matern
member has, prop:matern-exponent(3)). Right: the same on a logarithmic scale, where the Matern
tails are straight lines and the Gaussian is a parabola.

The kernels are computed by numerical Fourier inversion of the transform -- no Bessel function
and nothing cited -- so the picture rests on the transform of prop:two-members alone. The
gamma = 1 curve is checked against the Laplace kernel e^{-|x|}/2, which prop:matern-exponent's
transform identity gives in closed form. numpy and matplotlib only.

Run:  python scripts/make-fig-members.py      Out:  figures/fig-members.png
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures", "fig-members.png")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
plt.rcParams.update({"font.size": 9.5, "axes.linewidth": 0.8})

# Fourier inversion on a grid: phi(x) = (1/2 pi) int (1 + w^2)^(-gamma) e^{i w x} dw.
N = 2 ** 21
W = 4000.0                       # cutoff in omega; the tail beyond it matters only at |x| < 1/W
w = (np.arange(N) - N // 2) * (2 * W / N)
dw = w[1] - w[0]
x = np.fft.fftshift(np.fft.fftfreq(N, d=dw / (2 * np.pi)))   # x grid, spacing pi / W


def matern(gamma):
    F = (1.0 + w ** 2) ** (-gamma)
    phi = np.fft.fftshift(np.fft.ifft(np.fft.ifftshift(F))).real * N * dw / (2 * np.pi)
    return phi


# check: gamma = 1 is the Laplace kernel e^{-|x|}/2 (prop:matern-exponent(2) at t = 1, inverted)
phi1 = matern(1.0)
sel = (np.abs(x) > 0.05) & (np.abs(x) < 8)
err = np.max(np.abs(phi1[sel] - 0.5 * np.exp(-np.abs(x[sel]))))
print(f"gamma=1 vs Laplace kernel, max abs error on 0.05<|x|<8: {err:.2e}")
assert err < 1e-3

fams = [(0.5, "#d1495b", r"$\gamma=\frac{1}{2}$"), (1.0, "#6a4c93", r"$\gamma=1$ (Laplace)"),
        (2.0, "#2a9d8f", r"$\gamma=2$"), (4.0, "#1b6ca8", r"$\gamma=4$")]
curves = {g: matern(g) for g, _, _ in fams}
gauss = np.exp(-x ** 2 / 8.0) / np.sqrt(8 * np.pi)          # variance 4 = 2*gamma at gamma = 2

fig, (axl, axr) = plt.subplots(1, 2, figsize=(8.6, 3.3))
lin = np.abs(x) <= 4.0
for g, col, lab in fams:
    axl.plot(x[lin], curves[g][lin], color=col, lw=1.6, label=lab)
axl.plot(x[lin], gauss[lin], color="#555555", lw=1.6, ls="--", label=r"Gaussian, variance $4$")
axl.set_xlim(-4, 4); axl.set_ylim(0, 0.8)
axl.set_xlabel(r"$x$"); axl.set_ylabel(r"$\phi_1(x)$")
axl.set_title(r"linear scale: smoothness at the origin rises with $\gamma$", fontsize=9.5)
axl.legend(fontsize=7.5, frameon=False)

logsel = (x >= 0) & (x <= 12)
for g, col, lab in fams:
    axr.semilogy(x[logsel], curves[g][logsel], color=col, lw=1.6, label=lab)
axr.semilogy(x[logsel], gauss[logsel], color="#555555", lw=1.6, ls="--")
axr.set_xlim(0, 12); axr.set_ylim(1e-6, 1)
axr.set_xlabel(r"$x$")
axr.set_title(r"log scale: exponential tails at every $\gamma$", fontsize=9.5)
for ax in (axl, axr):
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(OUT, dpi=200)
print("wrote", OUT)
