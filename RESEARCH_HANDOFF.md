# RESEARCH_HANDOFF · 完美匹配树独立集多项式的任意末端对数凹凸模式

2026-11-27。数学证明已闭合，可以切换至 Sol。接手入口是本文和 `Audit.lean`。若只想核验主结论，先读下文的计数夹逼、全局取等和平衡标号交换，再看 `Geometry.matched_tree_every_word` 的编译记录。本目录的 `paper.tex` 是此前已经写成的同一证明的英文稿。

## 主定理及量词

有限树 T 的独立集多项式为 $I(T;x)=\sum_k a_kx^k$，独立数为 $\alpha$。令 $A_r=a_{\alpha-r}$。对任意整数 $L\ge1$ 及任意 $\varepsilon\in\{-1,+1\}^L$，存在**一棵**有完美匹配、直径至多 10、顶点数严格小于 $2^{15}(L+1)^7$ 的树 T，使

$$\operatorname{sgn}(A_{r-1}A_{r+1}-A_r^2)=\varepsilon_r\quad(1\le r\le L).$$

正号表示严格对数凸，负号表示严格对数凹。固定同一个词，有一族同一核心、整数尺度 $p\to\infty$ 的树，在该词的全部位置，比值 $A_{r-1}A_{r+1}/A_r^2$ 同时分别趋于无穷或零。顶点数界指其中一个有限尺度的见证。全正词可以用 $O((L+1)^6)$ 个顶点。没有断言尺度 1 可行、最大度有界、构造最小或独立集序列不单峰。

## 完整书面证明

**1. 拆点与系数。** 从一棵有 d 个标号的有向核心树开始。每个核心点 v 带两个非负整数权重 $(\lambda_v,\mu_v)$。增接 $p\lambda_v$ 个由 v 指向的新叶标号和 $p\mu_v$ 个指向 v 的新叶标号。令 $W=\sum_v(\lambda_v+\mu_v)$，总标号数 $m=d+pW$。每个标号 x 换成一条边 $x^+x^-$，原箭头 $u\to v$ 换成边 $u^+v^-$。图连通，有 $2m$ 点、$2m-1$ 边，故为树。标号内部的边构成完美匹配。全选正端独立，每条匹配边至多取一端，故 $\alpha=m$。

独立集正好是所有标号的三态配置 $+, -,0$，每条箭头只禁止源为正、目标为负。缺额等于状态为 0 的标号数，称为空位。合法核心配置 $\sigma$ 的分数 $e(\sigma)$ 逐点求和，正态贡献 $\mu_v$，负态贡献 $\lambda_v$，空态贡献两者之和。能任选两种非空符号的叶标号恰有 $p e(\sigma)$ 个。设 $M_r$ 是至多 r 个核心空位下的最大分数。若它可由**恰好** r 个核心空位取得，则

$$2^{pM_r}\le A_r\le {m\choose r}2^d 2^{pM_r}.\tag{1}$$

下界固定此核心，将所有叶填满。上界先选全体 r 个空标号，再指定非空核心标号的符号，其余自由的非空叶至多有 $pM_r$ 个。这个上界允许叶为空，且允许核心所用空位少于 r。

**2. 单组收益。** 设 $h\ge1$，$f(0)=0$，f 是 $[0,h]$ 上取非负整数值、非降、超可加的函数，$B=f(h)$。设共同源 y 权重为零。对每个 $s=1,\ldots,h$ 放一个中心 $z_s$，箭头 $y\to z_s$，另放 s 个分支 $u_i\to z_s$。分支权重 $(B,2B)$，中心权重 $(f(s),0)$。不同组只有 y 公用。将 y 改成负态永远不损失分数，只会释放可能的空位并解除限制。因此比较上界可假定 y 为负，取等见证也固定此状态。

若有 k 个分支为空，中心为正、空、负时，最大分数分别是 $2Bs+Bk,\ 2Bs+Bk+f(s),\ Bs+2Bk+f(s)$，用掉的空位分别为 $k,k+1,k$。中心为负时其余分支都必须为负。若预算 $q<s$，空中心的额外收益至多 B，可由它多用的空位支付；负中心相对正中心的差为 $f(s)-B(s-k)\le0$。若 $q\ge s$，空掉全部分支、中心为负即可释放全组所有叶。于是相对基线 $2Bs$，预算至多 q 时最大收益正好是

$$g_s(q)=B\min(q,s)+f(s)\mathbf 1_{q\ge s}.\tag{2}$$

**3. 多组共享空位。** 若 $\sum_s q_s\le r\le h$，线性部分之和不超过 Br。达到门槛的组构成 $J=\{s:q_s\ge s\}$，有 $\sum_{s\in J}s\le r$。重复超可加性和单调性给出 $\sum_{s\in J}f(s)\le f(r)$；空集由 $f(0)=0$ 处理。令 $E_0=2B\sum_{s=1}^h s$。若 $r>0$，把 r 个空位全给大小为 r 的组，使其中心为负，其余组的中心和分支全取正；$r=0$ 时全用各组基线。故

$$M_r=E_0+Br+f(r),\qquad 0\le r\le h.\tag{3}$$

上界允许任意分摊，取等见证恰用 r 个空位。这一区别对于 (1) 的下界必不可少。

**4. 首位为正的词。** 若 $h\ge2$ 且后缀 $\eta_1,\dots,\eta_{h-1}$ 首位为正，设 $d_0=h,\ d_i=d_{i-1}+\eta_i$，$v_j=\sum_{i=0}^{j-1}d_i$。各斜率为正，$0\le v_j\le v_h\le2h^2$。令 $D=2v_h+1$，设 $f(0)=0$，对 $j\ge1$ 取 $f(j)=D(2j-1)+v_j$。它递增。对正 a,b 且 $a+b\le h$，超可加盈余为 $D+v_{a+b}-v_a-v_b\ge1$，有零加数时恰相等。第一项二阶差分是 $D+1$，后续二阶差分恰为相应的 $\eta_i$。这里二阶差分取左右邻项之和减去中项两倍。由 $D\le5h^2$ 得 $B\le12h^3$。全正词也可用 $f(j)=j^2$。

**5. 任意长负前缀。** 令 $H=L+1$，t 为开头负号数，$h=H-t\ge1$。使用第 4 步编码剩余的 $h-1$ 个符号。若后缀空，取 $h=1,f(j)=j^2$。从 y 再发出 t 条箭头，各接一独立核心标号 $c_i$，其两种权重相等，均为 $w_i=2B+t-i+1$。每一非空态贡献 $w_i$，空态贡献 $2w_i$。

由 (2)，任一正的组预算减一，最优收益损失至多 $B+f(s)\le2B$，在饱和点和超饱和处也成立。如果一个平衡标号仍非空，而任何一组有正预算，就可给该组减少一单位预算，重选其配置并空掉平衡标号，严格获益。若总预算未用尽，也可直接空掉这个标号。已用的平衡标号中优先选最大权重。故前 $\min(t,r)$ 个单位给平衡标号，剩余 $k=\max(0,r-t)\le h$ 给各组。以 $C_0=E_0+\sum_i w_i$ 计，

$$M_r=C_0+\sum_{i=1}^{\min(t,r)}w_i+Bk+f(k),\qquad 0\le r\le H.\tag{4}$$

由第 3 步取等总是恰用 r 个核心空位。前 t 个边际增量是严格递减的 $w_1,\dots,w_t$。若 $t>0$，下一增量 $B+f(1)\le2B<w_t$，因而交界处仍严格为负。此后只剩 f 的平移二阶差分。此论证包括 $t=0,t=L,L=1$；最后一处用到 $M_{L+1}$，已包含在范围内。

**6. 搬回真实整数系数。** 令 $C=2^dm^H$。由 (1) 得 $2^{pM_r}\le A_r\le C2^{pM_r}$，包括 $r=0,H$。固定词时 $\log_2 C=O(\log p)$，所以归一化对数比值 $p^{-1}\log_2(A_{r-1}A_{r+1}/A_r^2)$ 收敛于 $\Delta^2 M_r$，有限多个位置同时成立。若 $C^2<2^p$，整数二阶差分的绝对值至少为 1，直接比较上下界即得严格符号。例如正差分给出 $A_r^2\le C^2 2^{2pM_r}<2^{p(2M_r+1)}\le A_{r-1}A_{r+1}$；负差分交换两个乘积。

取 $p=128H^2$，$S=h(h+1)/2$。此时 $d=1+h+S+t\le3H^2$，$W=3BS+\sum_s f(s)+2\sum_i w_i\le100H^5$（$S\le H^2,B\le12H^3,w_i\le25H^3$）。于是 $m<2^{14}H^7$，且 $2\log_2 C\le2d+2H(14+7H)\le48H^2<p$。全正词取平方函数使 $W=O(H^4)$。最后，各分支远端的路径为 $y^+,z_s^-,u_i^+,u_i^-$。在其上附叶至多再走两条边。中心和平衡标号的两个端点距 $y^+$ 至多 2，它们的叶端点至多 4。共同源的负端距正端 1。故所有点到 $y^+$ 距离至多 5，直径至多 10。证毕。

## 证明依赖与形式化对齐

|数学步骤|可检查的 Lean 声明或文件|
|---|---|
|逐组最优和分摊预算|TerminalCurvature.star_bound、star_attains、atlas_bound、atlas_active、atlas_exact|
|跨过饱和点仍可移走一个预算|gain_step、trim_allocation；Word.lean 中 main_certificate 建立全预算上包络，在目标区间逐点取等|
|任意正起始后缀和负前缀|bonus_profile、bonus_curvature_first/later、balanced_certificate、prepend_negative、every_word。Certificate.exact 同时给至多 r 上界与恰 r 见证|
|标明身份的实际核心点与压缩计数等价|Assembly.star_realises、stars_realises、device_realises，最后一个是双向等价|
|实际顶点子集计数|Counting.layerEquiv、lower_count、upper_count；Family.free_card 和 count_bounds 在同一构造上消去计数假设|
|符号搬运及结构|Family.transfer_word、physical_every_word；Geometry.parent_step、parent_orientation、acyclic、diameter_ten、perfect_matching、independence_number|
|主形式化命题|Geometry.matched_tree_every_word 对每个 List Bool 同时给出上述符号与图性质，true 对应严格凸，索引 i=0 对应正文 r=1；两边使用同一 c,p、同一邻接和计数定义|

Lean 中 `PhysicalLayer` 是满足独立性和 $|S|+r=m$ 的有限顶点子集。直径用任意两点间长度至多十的逐边 walk 表达，故也给连通性。无环性用每个非空顶点集有一个内部度数至多 1 的点表达；简单圈的顶点集立刻违反此性质。匹配是实际边上的无不动点对合。形式化主命题使用这些透明定义，没有依赖一个假设图性质成立的接口。

**形式化边界。** 同一匹配树上实现每个词并保持直径界，已贯通。一般存在性模块为尺度选择使用比正文更粗的、依赖具体核心的参数 $N=d+W+H+1$，取 $128N^2$。它在空后缀的单组也可用通用 bonus 函数，与正文的较小平方权重有别，两者均满足所需性质。`explicit_scale` 已验证给定 d,m 界后的整数分离。正文的 $2^{15}H^7$ 阶数界、全正词 $O(H^6)$ 和真实比值的极限已有上面的书面证明，尚未作为对应的完整 Lean 定理封装。具体 736 点例子的普通树递推用内核直接计算；它不承担一般性证明。

## 对抗性复核与实验证据

- 逐式检查的风险包括多个组同时到门槛、中心本身为空、公共源为空、真实缺额落在叶上、组跨过饱和点、全负词、后缀仅一位、参数 p 被提前固定、末端索引差一。步骤 1–6 分别给出通用处理；不需要不同位置使用不同的树或不同的 p。
- `records/core_stress.json` 由独立 C++ 三态树动态规划得到，未调用 (2) 求最优值。长度 1–12 的全部 8,190 个词共 106,494 个预算，另有 91 个长词、10,361 个预算，最长 256。删去超可加性的负对照在缺额 3 得到真实最优 85、预测 80。降低平衡权重的负对照在缺额 1 得到 30 对 26。具体参数在程序末尾。
- `records/verification.json` 包含长度 1–7 全部 254 个词的精确整数系数验证，508 次配置/尺度检查，18 个小核心共 257,310 个三态，3,168 个单星边界检查，26 次展开树与分组计数交叉核验，65 次直接子集枚举。小参数策略在 195 个词上取 p=1 失败；特例 $f=(0,1,4)$，首个比值在 p=1 约 0.521，在 p=2 约 2.819。只有“这些有限测试在 p≤4 都找到见证”有计算证据；一般定理不使用这个小尺度猜想。
- `records/scales.json` 记录九个按正文统一尺度计算真实系数的样本，三例另用展开图核算。最大样本 25,154,598 顶点，用分组整数法。没有用这些有限结果推断全称命题。

## 相关文献与原创性状态

截至 2026-11-27，检索 arXiv 题录与全文、期刊原文和公开研究存档，回查相关论文引用。检索组合包括 independence polynomial / independent set sequence、tree with perfect matching、terminal coefficients、arbitrary sign pattern、prescribed and simultaneous failures、consecutive log-concavity failures、weighted core、Turán determinants。以下是影响新颖性判断的最接近来源。

1. H. Fan，*Prescribed and simultaneous failures of log-concavity in trees with perfect matchings*，arXiv:2610.18340，2026。任意指定单个缺额、或奇数缺额同时失效；匹配标号编码、自由叶指数方法来自该文。https://arxiv.org/abs/2610.18340
2. X. Yu，*Unbounded runs of non-log-concavity in independence polynomials of trees*，Zenodo v1.1.0，2026。一般树上任意长失效区间已公开。https://doi.org/10.5281/zenodo.22263331
3. C. Bautista-Ramos、C. Guillén-Galván、P. Gómez-Salgado，*Linear Recurrences for Non-Log-Concave Independence Polynomials of Trees*，Graphs and Combinatorics 42, 59 (2026)。连续至五处失效的相关结果。https://doi.org/10.1007/s00373-026-03054-4
4. Evidence Press，*Log-concavity transitions in sums of polynomial powers*，2026-11-15 候选稿。声称直径四已有任意长失效区间。https://www.evidencepress.org/releases/tree-log-concavity-diameter-four/
5. D. Galvin，arXiv:2502.10654；C. Bautista-Ramos，arXiv:2511.00334；O. Kadrawi、V. E. Levit，arXiv:2305.01784。早期例子和多处失效的背景，书目在 paper.tex。

本次检索尚未见同时满足“紧贴独立数、逐位置任意指定正负、同一棵完美匹配树、绝对直径界”的同一定理。新增数学步骤是超可加剖面的精确实现和处理任意负前缀的交换。优先权尚待独立同行核查。

## 复现与下一位模型的工程任务

Lean 4.19.0 和 mathlib v4.19.0。实际编译输出收在 `records/lean-audit.txt`。项目目录结构保持平铺。已安装 elan 和 Git 且可联网时，从解压目录运行：

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

本轮实际检查使用固定版本的本地 mathlib 缓存，依序对 TerminalCurvature、Word、Counting、Assembly、Family、Geometry、ExplicitTree、Audit 直接运行 lean -o。上述八个模块已从空的本项目编译输出目录全部通过。主定理依赖 propext、Classical.choice、Quot.sound。具体递推见证 ExplicitTree.mixed_witness 无公理依赖。源码无 sorry 占位、用户公理或 native_decide。可在独立目录按同样版本再做 Lake 复现。

已有的实验只需在复现时运行；无须继续扩大样本：

```sh
python3 -O verify.py > verification.json
c++ -O2 -std=c++17 -Wall -Wextra -Werror stress_core.cpp -o stress_core
./stress_core > core_stress.json
python3 -O check_scales.py > scales.json
python3 -O verify.py --word '+-+-' --scale 2
```

前三个 JSON 可同 records 中的同名输出比对。实验主要使用 Python 标准库及 C++17，无外部数据。

如需机器命题与书面定量界完全一致，Sol 可在 every_word 的归纳证书中附加 d、W 和边际步长上界，正起始分支用 $B\le12H^3$，每前置一个负号增加一个标号与两倍新权重，再调用 label_card、explicit_scale、transfer_word。全正特例单独使用平方剖面。若需要形式化极限，使用 count_bounds 取对数并除以 p，对固定核心的误差为 $O((\log p)/p)$。若其他项目要求 mathlib.SimpleGraph.IsTree，可增加同构和标准谓词的适配引理。以上均为已证数学结论的工程收尾。本阶段未投稿。
