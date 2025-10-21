\begin{proof}
Fix $n\ge3$. By the quadratic packing lower bound together with a standard transference principle, there is a unimodular lattice $L\subset\R^n$ with
\[
\Delta(L)\ \ge\ c_0\,n^2\,2^{-n}
\]
for an absolute $c_0>0$, and whose minimum $\lambda(L)$ and covering radius $\mu(L)$ obey
\[
 c_1\,n\ \le\ \mu(L)\,\lambda(L)\ \le\ C_1\,n
\]
with absolute $c_1,C_1>0$. Using Stirling, $\omega_n^{1/n}\asymp\sqrt{2\pi e/n}$, we obtain
\[
\lambda(L)\ \ge\ c\sqrt n,\qquad \mu(L)\ \le\ C\sqrt n
\]
for absolute $c,C>0$. Let $K:=V(L)$ be the Voronoi cell. Then
\[
B_n\!\bigl(0,\tfrac{\lambda(L)}2\bigr)\ \subset\ K\ \subset\ B_n\!\bigl(0,\mu(L)\bigr),
\]
so, writing $r_-:=\tfrac{\lambda(L)}2$ and $r_+:=\mu(L)$, we have $r_-\ge c\sqrt n$ and $r_+\le C\sqrt n$.

Let $X$ be uniform in $K$ and write $R:=\|X\|$. For $\theta\in\S^{n-1}$ let the radial function be
\[
 r(\theta):=\sup\{t\ge0:\ t\theta\in K\}.
\]
Then $X$ admits the usual polar-factor representation: if $\Theta$ has density $r(\theta)^n/\int r^n\,d\sigma$ on $\S^{n-1}$ and $U\sim\mathrm{Unif}[0,1]$ is independent of $\Theta$, then
\[
 R\stackrel d= r(\Theta)\,U^{1/n}.
\]
Equivalently, conditionally on $\Theta=\theta$, $R$ has CDF $\Pr[R\le s\mid\Theta=\theta]=(s/r(\theta))^n$ for $0\le s\le r(\theta)$.

We now control the angular oscillation of the logarithmic radius. Let $K^{\circ}$ be the polar body and $h:=h_{K^{\circ}}$ its support function. For $u\in\S^{n-1}$,
\[
 r(u)=\frac{1}{h(u)}.
\]
From $B(0,r_-)\subset K\subset B(0,r_+)$, polarity yields $B\bigl(0,1/r_+\bigr)\subset K^{\circ}\subset B\bigl(0,1/r_-\bigr)$. Using the triangle inequality for $h$,
\[
 |h(u)-h(v)|\le h(u-v)\le \frac1{r_-}\,\|u-v\|_2\qquad(u,v\in\R^n),
\]
and hence, for $u,v\in\S^{n-1}$,
\[
 |r(u)-r(v)|=\Big|\tfrac1{h(u)}-\tfrac1{h(v)}\Big|\le \frac{|h(u)-h(v)|}{h(u)h(v)}\le \frac{r_+^2}{r_-}\,d_{\S}(u,v).
\]
Therefore $\phi:=\log r$ is $L_0$–Lipschitz on $\S^{n-1}$ with
\[
 L_0\ \le\ \frac{r_+^2/r_-}{\inf r}\ \le\ \frac{r_+^2}{r_-^2}\ \le\ \Big(\frac{C}{c}\Big)^2=O(1).
\]

Introduce
\[
 Z(a):=\log\int_{\S^{n-1}} e^{a\phi(\theta)}\,d\sigma(\theta)\qquad (a\in\R),
\]
so that $Z'(a)=\E_{\Pi_a}[\phi]$ and $Z''(a)=\Var_{\Pi_a}(\phi)$, where $\Pi_a$ is the probability on $\S^{n-1}$ with density $e^{a\phi}/\int e^{a\phi}d\sigma$. The angular law of $\Theta$ equals $\Pi:=\Pi_n$.

Claim 1 (uniform sub-Gaussian curvature). There exists an absolute $C_* > 0$ such that for all $a\in\R$,
\[
 Z''(a)=\Var_{\Pi_a}(\phi)\ \le\ \frac{C_*}{n}.
\]
Proof. Since $\phi$ is $L_0$–Lipschitz with $L_0=O(1)$, the log–Sobolev/Herbst bound on $\S^{n-1}$ implies that for all $\lambda\in\R$, $\log\E_{\sigma}\exp(\lambda(\phi-\E_\sigma\phi))\le (C/n)\lambda^2$ with an absolute $C$. Writing $H(\lambda):=\log\E_{\sigma}e^{\lambda(\phi-\E_\sigma\phi)}$, we have $Z(a)=a\E_\sigma\phi+H(a)$ and $H(\lambda)\le (C/n)\lambda^2$. The convexity inequality $H(a+s)+H(a-s)-2H(a)\le(2C/n)s^2$ yields (letting $s\to0$) $H''(a)\le 2C/n$ for all $a$. Hence $Z''(a)=H''(a)\le C_*/n$ with $C_*:=2C$. \qed

A standard Taylor argument with Claim 1 gives the angular sub-Gaussian mgf bound at the Gibbs law $\Pi$:
\begin{equation}
\log\E_{\Pi}e^{t(\phi-\E_{\Pi}\phi)}\ =\ Z(n+t)-Z(n)-tZ'(n)\ \le\ \frac{C_*}{2n}\,t^2\qquad(t\in\R).
\label{eq:ang-mgf}
\end{equation}
Consequently, by Chernoff, for some absolute $c_0>0$ and all $s\ge0$,
\begin{equation}
 \Pi\big[\,|\phi(\Theta)-\E_{\Pi}\phi|\ge s\,\big]\ \le\ 2\exp\bigl(-c_0\,n\,s^2\bigr).
\label{eq:ang-conc}
\end{equation}

Next we relate $\E_{\Pi}\phi$ to $\sqrt{\E R^2}$. Conditioning on $\Theta=\theta$ gives $\E[R^2\mid\Theta=\theta]=\tfrac{n}{n+2}r(\theta)^2$. Hence
\[
\E R^2\ =\ \frac{n}{n+2}\,\frac{\int e^{(n+2)\phi}\,d\sigma}{\int e^{n\phi}\,d\sigma}
\ =\ \frac{n}{n+2}\,\exp\bigl(Z(n+2)-Z(n)\bigr),
\]
so
\[
\log\sqrt{\E R^2}\ =\ \tfrac12\log\tfrac{n}{n+2}\ +\ \tfrac12\bigl(Z(n+2)-Z(n)\bigr).
\]
Using Claim 1,
\[
Z(n+2)-Z(n)-2Z'(n)\ =\ \int_0^2 (2-s)\,Z''(n+s)\,ds\ \le\ \frac{2C_*}{n},
\]
while $\tfrac12\log\tfrac{n}{n+2}=-\tfrac{1}{n}+O(\tfrac1{n^2})$. Hence there is an absolute $C_2>0$ such that
\begin{equation}
 \bigl|\,\log\sqrt{\E R^2}\ -\ \E_{\Pi}\phi\,\bigr|\ \le\ \frac{C_2}{n}.
\label{eq:center-shift}
\end{equation}

We now establish a sub-Gaussian bound for the logarithmic radius itself. Write
\[
\log R\ =\ \phi(\Theta)\ +\ \frac1n\log U,
\]
where $U\sim\mathrm{Unif}[0,1]$ is independent of $\Theta$. For $t>-n$,
\begin{align*}
\log\E\exp\bigl(t(\log R-\E_{\Pi}\phi)\bigr)
&= \log\E_{\Pi}\exp\bigl(t(\phi-\E_{\Pi}\phi)\bigr)\ -\ \log(1+t/n)\\
&\le \frac{C_*}{2n}t^2\ -\ \log(1+t/n),
\end{align*}
using \eqref{eq:ang-mgf} and $\E[U^{t/n}]=1/(1+t/n)$. For $t\in[0,n/2]$, $-\log(1+t/n)\le0$, hence
\begin{equation}
\log\E\exp\bigl(t(\log R-\E_{\Pi}\phi)\bigr)\ \le\ \frac{C_*}{2n}t^2\qquad(0\le t\le n/2).
\label{eq:logR-mgf-pos}
\end{equation}
For $t\in[-n/2,0]$, the elementary bound
\begin{equation}
-\log(1+t/n)\ \le\ \frac{2|t|}{n}\qquad(-n/2\le t\le0)
\label{eq:logineq}
\end{equation}
(indeed, $g(x)=-2x+\log(1+x)$ is decreasing on $[-\tfrac12,0]$ and $g(0)=0$) yields
\begin{equation}
\log\E\exp\bigl(t(\log R-\E_{\Pi}\phi)\bigr)\ \le\ \frac{C_*}{2n}t^2+\frac{2|t|}{n}\qquad(-n/2\le t\le0).
\label{eq:logR-mgf-neg}
\end{equation}

Chernoff’s method applied to \eqref{eq:logR-mgf-pos} gives, for all $s\in[0,1]$,
\begin{equation}
\Pr\big[\log R-\E_{\Pi}\phi\ge s\big]\ \le\ \exp\Big(-\frac{n}{2C_*}\,s^2\Big).
\label{eq:upper-logR}
\end{equation}
For the lower tail, using \eqref{eq:logR-mgf-neg} with the choice $t=-\tfrac{n s}{8C_*}$ (which lies in $[-n/2,0]$ for $s\le1$), we obtain
\[
\Pr\big[\log R-\E_{\Pi}\phi\le -s\big]\ \le\ \exp\Big(-\frac{n}{8C_*}s^2+\frac{n}{128C_*}s^2+\frac{s}{4C_*}\Big)
\ \le\ \exp\Big(-\frac{n}{16C_*}s^2\Big)
\]
whenever $s\ge \tfrac{5}{n}$; for $0\le s\le\tfrac{5}{n}$ the bound is trivial since $\Pr[\cdot]\le1\le 2e^{-cns^2}$ after reducing $c>0$ if needed. Combining the two tails, there is an absolute $c_1>0$ such that, for all $s\in[0,1]$,
\begin{equation}
 \Pr\big[\,|\log R-\E_{\Pi}\phi|\ge s\,\big]\ \le\ 2\exp\big(-c_1\,n\,s^2\big).
\label{eq:logR-around-Epi}
\end{equation}

Using the center shift \eqref{eq:center-shift} and the inclusion
\[
 \big\{\,|\log R-\log\sqrt{\E R^2}|\ge s\,\big\}\ \subset\ \big\{\,|\log R-\E_{\Pi}\phi|\ge s-\tfrac{C_2}{n}\,\big\},
\]
we obtain, for $s\in[0,1]$,
\begin{equation}
 \Pr\big[\,|\log R-\log\sqrt{\E R^2}|\ge s\,\big]\ \le\ 2\exp\Big(-c_1\,n\,(s-\tfrac{C_2}{n})_+^2\Big)\ \le\ 2\exp\big(-c\,n\,s^2\big)
\label{eq:log-shell}
\end{equation}
for an absolute $c>0$ (adjusting constants).

Finally, convert the logarithmic bound into the Euclidean one. Since $r_-\ge c\sqrt n$ and $r_+\le C\sqrt n$, we have $\sqrt{\E R^2}\in[c\sqrt n, C\sqrt n]$. For $0\le t\le1$, the mean value theorem yields
\[
 \bigl|\log(\sqrt{\E R^2}\pm t\sqrt n)-\log\sqrt{\E R^2}\bigr|\ \ge\ \frac{t\sqrt n}{\sqrt{\E R^2}+t\sqrt n}\ \ge\ \frac{t}{C+1}=:\kappa t.
\]
Hence
\[
 \big\{\,|R-\sqrt{\E R^2}|\ge t\sqrt n\,\big\}\ \subset\ \big\{\,|\log R-\log\sqrt{\E R^2}|\ge \kappa t\,\big\}\qquad(0\le t\le1).
\]
Applying \eqref{eq:log-shell} with $s=\kappa t$ gives
\[
 \Pr\Big[\,\big|\|X\|-\big(\E\|X\|^2\big)^{1/2}\big|\ \ge\ t\sqrt n\,\Big]\ \le\ 2\exp\big(-c'\,t^2 n\big)\qquad(0\le t\le1)
\]
for an absolute $c'>0$. All constants are absolute and depend only on the sandwiching constants $c,C$. This proves the stated thin-shell concentration.
\end{proof}