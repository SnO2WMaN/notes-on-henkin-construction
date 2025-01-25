#import "template.typ": *

#show: project.with(
  title: "Henkin構成による完全性定理の証明",
  authors: ("SnO2WMaN",),
)

#let Lang = $cal(L)$
#let Model(M) = $frak(#M)$


1階述語論理の完全性定理をHenkinの構成を用いて証明する．参考文献は @kikuchiIncompleteness2014．

= 準備

#notation[
  - 以下では1階述語論理の事実を考えているとする．
  - $Lang$ は言語とする．
  - $T$ は $Lang$ の理論とする．
]

#definition[無矛盾性][
  $T nvdash bot$ であるとき，$T$ は無矛盾であるという．
]

古典論理では次が成り立つ．

#lemma[
  $T nvdash sigma$ な $sigma$ が存在するなら $T$ は無矛盾である．
]
#proof[爆発律より明らか．]

#lemma[
  次は同値．
  1. $T union {not sigma}$ が無矛盾である．
  2. $T nvdash sigma$．
]<lem:iff_consistent>
#proof[
  対偶を示す．$T union {not sigma}$ が矛盾するなら $T, not sigma vdash bot$ であり，演繹定理と二重否定除去より $T vdash sigma$ である．
  逆に $T vdash sigma$ なら，二重否定導入より $T vdash not not sigma$ であり，演繹定理より $T, not sigma vdash bot$ であり，$T union {not sigma}$ は矛盾する．
]

#lemma[
  $T$ が無矛盾かつ $T vdash sigma$ なら $T union {sigma}$ は無矛盾．
]<lem:consistent_add_of_provable>

#definition[極大無矛盾性][
  $T$ の真の無矛盾な拡大理論が存在しないとき，$T$ は極大無矛盾であるという．
]

#lemma[
  $T$ は極大無矛盾とする．$T vdash sigma$ と $sigma in T$ は同値．
]<lem:iff_maximal_provable_mem>
#proof[
  $sigma in T$ なら $T vdash sigma$ なのは明らか．

  $T vdash sigma$ ならば $T union {sigma}$ は無矛盾．
  仮に $sigma in.not T$ なら $T union {sigma}$ は $T$ の無矛盾な真の拡大理論だが，$T$ が極大無矛盾なのでそれはありえない．
  よって $sigma in T$．
]

#lemma[
  以下は同値．

  1. $T$ が極大無矛盾．
  2. 全ての $sigma$ に対して $sigma in T$ または $not sigma in T$ が成り立つ．
]<lem:iff_maximal_consistent>

#proof[
  #struct[
    1.から2.を示す．
    $T vdash sigma$ なら @lem:iff_maximal_provable_mem より $sigma in T$．
    $T nvdash sigma$ なら $T union {not sigma}$ は無矛盾．$T$ が極大無矛盾なので $not sigma in T$．
  ]
  #struct[
    2.から1.を示す．対偶を示す．
    $T$ が極大無矛盾でないとすると，$T$ の真の無矛盾な拡大理論 $U$ が存在する．
    $sigma in U without T$ とすると，$not sigma in T$ なら $not sigma in U$ であり，$U$ が矛盾する．
    よって $not sigma in.not T$．当然 $sigma in.not T$ であるので示された．
  ]
]

/*
#proposition[弱Kőnigの補題][
  無限個の頂点を持つ2分木は無限長の枝を持つ．
] <prop:weak_konig_lemma>
*/

#lemma[Lindenbaum補題][
  $T$ が無矛盾ならば $T subset.eq U$ となる極大無矛盾な拡大理論 $U$ が存在する．
]<lem:lindenbaum>
#proof[
  $Lang$-文を列挙して $sigma_0, sigma_1, ...$ とする．
  $sigma_i, not sigma_i$ によって枝分かれする完全無限2分木を作る．
  この木の枝と，枝に現れる文の集合とを同一視することにする．

  この木には $T$ と矛盾しない無限の長さを持つ枝が存在する．
  // 枝上に現れる文と $T$ とが無矛盾になるように適当に枝を剪定する．このようにしても木は無限木である．
  #struct[
    // 仮に木が無限木ではないとすると，2分木なので木の高さが有限である．
    存在しないと仮定すると，任意の枝についてその枝の先端部分までの ${sigma_0, ..., sigma_n}$ に $sigma_(n + 1)$ または $not sigma_(n + 1)$ のどちらを加えても $T$ とは矛盾する：これ以上は伸ばせない．

    仮に，$sigma_(n + 1)$ を加えると矛盾するならば，$T, sigma_0, ..., sigma_n, sigma_(n + 1) vdash bot$ である．
    演繹定理より $T, sigma_0, ..., sigma_n vdash sigma_(n + 1) -> bot$ すなわち $T, sigma_0, ..., sigma_n vdash not sigma_(n + 1)$ である．
    $T union {sigma_0, ..., sigma_n}$ は無矛盾なので
    @lem:consistent_add_of_provable より $T union {sigma_0, ..., sigma_n, not sigma_(n + 1)}$ も無矛盾である．
    しかし，これは仮定に反するのでおかしい．

    同様に $not sigma_(n + 1)$ を加えると矛盾するなら，$T union {sigma_0, ..., sigma_n, sigma_(n + 1)}$ が無矛盾であることが示されておかしい．

    よって，木の高さは無限であり，木は無限木である．
  ]

  // この木に対して，@prop:weak_konig_lemma より #footnote[木が無限木である証明から直ちに明らかで，@prop:weak_konig_lemma を使う必要は無い気がする．] 無限長の枝が存在する．
  このような無限長の枝から適当に一つ選び，この枝を $U$ とすると，これは極大無矛盾な拡大理論である．

  $U$ が $T$ を含むこと及び $T$ が無矛盾であることは明らか．
  $U$ が極大無矛盾であることは，@lem:iff_maximal_consistent から
  任意の文 $sigma$ に対して $sigma in U$ または $not sigma in U$ であることを示せばよく，これも枝の作り方と無限長であることより明らか．
]

= 完全性定理

#theorem[健全性定理][
  $T vdash sigma$ ならば $T vDash sigma$．
] <thm:soundness>
#proof[$sigma$ の論理式に関する帰納法．]

より強く，次の@lem:generalized_soundness が成り立つ．

#corollary()[
  $T$ がモデルを持つならば $T$ は無矛盾である．
]<lem:generalized_soundness>
#proof[
  $T$ がモデルを持つなら $T union {not bot}$ もモデルを持つので，$T nvDash bot$．
  @thm:soundness より $T nvdash bot$ なので，$T$ は無矛盾．
]

@thm:soundness の逆#footnote[正確に言えば，1.から2.の含意を狭義の完全性定理と呼び，同値すなわち@thm:completeness は広義の完全性定理という．]も成り立つ．

#theorem[完全性定理][
  次は同値．
  1. $T vDash sigma$．
  2. $T vdash sigma$．
] <thm:completeness>

これは一般化された形である@thm:generalized_completeness から従う．

#theorem[一般化された完全性定理][
  次は同値．
  1. $T$ が無矛盾．
  2. $T$ はモデルを持つ．
] <thm:generalized_completeness>

#proof[@thm:completeness][
  2.から1.は @thm:soundness より明らか．1.から2.を示す．

  $T vDash sigma$ なら $T union {not sigma}$ はモデルを持たず，@thm:generalized_completeness より $T union {not sigma}$ は矛盾する．
  このとき特に $T, not sigma vdash bot$ であり，演繹定理より $T vdash not not sigma$ で，二重否定除去より $T vdash sigma$．
]

@thm:generalized_completeness の片方は @lem:generalized_soundness そのものであるが，他方は明らかではない．
無矛盾な理論から実際にモデルを構成する方法の一つがHenkinの構成である．

= Henkinの構成

#notation[
  - $T$ は無矛盾とする．
  - 変数記号 $v_0$ を一つ固定する．
  - $v_0$ のみを自由変数とする $Lang$-論理式の集合を $F_Lang$ とする．
]

#let Consts = $cal(C)$

#definition[
  $i in omega$ とし，$Consts_i, Consts, Lang_i$ を以下のように定める．
  1. $Lang_0 := Lang$ とする．
  2. $F_(Lang_i)$ に対応する定数記号を $Consts_i := { c_phi | phi in F_(Lang_i)}$ とする．
    ただし $c_phi$ は $Lang_i$ の定数記号ではないものとする．
  3. $Lang_(i + 1) := Lang_i union Consts_i$ とする．
  4. $Consts := union.big_(i in omega) Consts_i$ とする．
]<def:henkin_lang>

#definition[Henkin公理][
  $phi(v_0) in F_(Lang union Consts)$ とする．
  次の $Lang union Consts$-文 $eta_phi$ を $phi$ に対するHenkin公理 とよぶ．
  $
    eta_phi :equiv exists v_0. phi(v_0) -> phi(c_phi)
  $
]

#let Henkinized(T) = $#T^upright("H")$

#definition[Henkin拡大理論][
  言語 $Lang union Consts$ の理論 $Henkinized(T) := T union { eta_phi | phi(v_0) in F_(Lang union Consts) }$ を $T$ のHenkin拡大理論という．
]

#lemma[
  $Henkinized(T) subset.eq U$ とする．以下は同値．
  1. $U vdash exists v. phi(v_0)$
  2. $U vdash phi(c_phi)$
]<lem:iff_henkinzed>
#proof[
  1.から2.は $U$ には $phi$ の Henkin公理が含まれていることから従う．
  2.から1.は明らか．
]

#lemma[
  $T$ は $Lang_i$ の理論，$phi(v_0)$ は $Lang_i$-論理式，$sigma$ は $Lang_i$-文とする．
  このとき，$T, eta_phi vdash sigma$ ならば $T vdash sigma$．
]<lem:henkin_axiom_removalbe>
#proof[
  演繹定理より $T vdash eta_phi -> sigma$ であり，展開すると $T vdash [exists v_0. phi(v_0) -> phi(c_phi)] -> sigma$．

  ここで定義より $c_phi in Lang_(i + 1)$ であることに注意すると，
  $T$ は $Lang_i$ の理論であるので，実際には $c_phi$ はこの演繹には現れることはない．
  よって，この演繹に含まれないフレッシュな変数記号 $w$ を取ってきて $c_phi$ を $w$ に置き換えることで
  $[exists v_0. phi(v_0) -> phi(w)] -> sigma$ は $Lang_i$-文として見ることができて，
  更に元の演繹によって $T vdash [exists v_0. phi(v_0) -> phi(w)] -> sigma$ が言える．

  $w$ に対して全称化をして $T vdash forall w. [[exists v_0. phi(v_0) -> phi(w)] -> sigma]$．
  更に適当な1階述語論理の計算によって $T vdash [exists v_0. phi(v_0) -> exists w. phi(w)] -> sigma$ が言える．
  前件は明らかなので $T vdash sigma$．
]

#remark[
  @def:henkin_lang で $c_phi$ は $phi$ が属する言語 $Lang_i$ の定数記号ではないものと保証したことがこの証明では効いている．
  この保証がなければ，$c_phi in Lang_(i + 1)$ すなわち $c_phi in.not Lang_(i)$ であることは言えず，適切な置き換えができない．
]

#lemma[
  $Henkinized(T)$ は $T$ の保存的拡大．
]
#proof[
  $sigma$ は $Lang$-文 とし，$Henkinized(T) vdash sigma$ と仮定して $T vdash sigma$ を示す．

  $Henkinized(T) vdash sigma$ の演繹上に現れるHenkin公理の集合を $H$ とすると，これは有限であり，$T union H vdash sigma$ である．
  今，$H$ に含まれる最も大きな言語 $Lang_i$ のHenkin公理を $eta_i$ とする．

  このとき，$T union (H without {eta_i}), eta_i vdash sigma$ であるから，
  @lem:henkin_axiom_removalbe より $T union (H without {eta_i}) vdash sigma$ である．

  これを $H$ の要素の数だけ繰り返せば，いずれ $T vdash sigma$ が得られる．
]

#corollary[
  $Henkinized(T)$ は無矛盾．
]<cor:henkinized_consistent>
#proof[無矛盾な保存的拡大理論は無矛盾であることから従う．]

#corollary[
  $Henkinized(T)$ を含む極大無矛盾な拡大理論が存在する．
]<cor:henkinized_lindenbaum>
#proof[
  @cor:henkinized_consistent と @lem:lindenbaum より．
]

#notation[
  以下，$T^*$ は @cor:henkinized_lindenbaum で得られる $Henkinized(T)$ の極大無矛盾な拡大理論とする．
]

#lemma[
  $phi(v_0) in F_(Lang union Consts)$ とする．
  $exists x. phi(x) in T^*$ ならば $phi(c_phi) in T^*$ である．
]
#proof[@lem:iff_maximal_consistent と @lem:iff_henkinzed より明らか．]

// 等号の解釈の都合，
#definition[
  $Consts$ 上の同値関係 $~$ を $c_1 ~ c_2 <==> c_1 = c_2 in T^*$ で定める．
  $c$ の $~$ による同値類を $tilde(c)$ と書く．
]

#remark[
  これが同値関係になることは，$=$ の等号としての性質が1階述語論理の等号の公理によって正当化されることから従う．
]

#definition[Henkinモデル][
  $Lang union Consts$ 上のモデル $Henkinized(Model(M))_T$ を，領域を $C slash ~$ として次のように定める．

  1. 定数記号 $c in Lang union Consts$ の $Henkinized(Model(M))_T$ での解釈は，$phi(v_0) :equiv v_0 = c$ として，以下のように定める．
    $
      c^(Henkinized(Model(M))_T) |-> tilde(c_phi)
    $

  2. $n$ アリティの関数記号 $f in Lang$ の $Henkinized(Model(M))_T$ での解釈は，$c_1, ..., c_n in Consts$，$phi(v_0) :equiv v_0 = f(c_1,...,c_n)$ として，以下のように定める．
    $
      f^(Henkinized(Model(M))_T)(tilde(c_1), ..., tilde(c_n)) |-> tilde(c_phi)
    $

  3. $n$ アリティの述語記号 $P in Lang$ の $Henkinized(Model(M))_T$ での解釈は，$c_1, ..., c_n in Consts$ として，以下のように定める．
    $
      P^(Henkinized(Model(M))_T)(tilde(c_1), ..., tilde(c_n)) <==> P(c_1, ..., c_n) in T^*
    $

  $Henkinized(Model(M))_T$ を $T$ のHenkinモデルという．
]

#remark[
  定数記号 $c$ の解釈について考える．$phi(v_0) :equiv v_0 = c$ とする．
  自明に $T^* vdash exists v_0. phi(v_0)$ であるから，$exists v_0. phi(v_0) in T^*$ であり @lem:iff_maximal_consistent より $phi(c_phi) in T^*$ である．
  したがって $c_phi = c in T^*$ であるので，$c in tilde(c_phi)$ である．

  関数記号 $f$ の解釈について考える．$c_1, ..., c_n in Consts$ として $phi(v_0) :equiv v_0 = f(c_1,...,c_n)$ とする．
  やはり同様に $exists v_0. phi(v_0) in T^*$ であるから，$phi(c_phi) in T^*$ であり $c_phi = f(c_1,...,c_n) in T^*$ である．
  したがって $f(c_1,...,c_n) in tilde(c_phi)$ である．これは代表元 $c_1, ..., c_n$ の取り方によらず定義されている．

  述語記号 $P$ の場合も代表元 $c_1, ..., c_n$ の取り方によらず定義されている．
]

#lemma[真理補題][
  任意の $Lang union Consts$-文 $sigma$ に対して，以下は同値．
  1. $sigma in T^*$
  2. $Henkinized(Model(M))_T vDash sigma$
]
#proof[
  $sigma$ の論理式に関する帰納法．
  #struct[
    $sigma$ が原子論理式の場合，および $bot$ の場合は $Henkinized(Model(M))_T$ の定義より明らか．
  ]
  #struct[
    $sigma :equiv sigma_1 -> sigma_2$ の場合については，
    $sigma_1 -> sigma_2 in T^*$ は $sigma_1 in.not T^*$ または $sigma_2 in T^*$ であることと同値であることに注意して，帰納法の仮定を使えばよい．
  ]
  #struct[
    $sigma :equiv forall x. phi(x)$ の場合について示す．$phi(x)$ は $x$ にのみ自由変数を持つ $Lang union Consts$-論理式とする．

    #struct[
      1.から2.を示す．
      任意の $tilde(c) in |Henkinized(Model(M))_T|$ に対して $Henkinized(Model(M))_T vDash phi(tilde(c))$ であることを示せばよい．

      任意に $tilde(c) in |Henkinized(Model(M))_T|$ を取る．
      $c in Consts$ に注意すると，$forall x. phi(x) in T^*$ より $phi(c) in T^*$ である．帰納法の仮定より，$Henkinized(Model(M))_T vDash phi(c)$ である．$Henkinized(Model(M))_T$ の解釈は代表元の取り方によらないので $Henkinized(Model(M))_T vDash phi(tilde(c))$ である．
    ]

    #struct[
      2.から1.を示す．
      対偶を示す．$forall x. phi(x) in.not T^*$ ならば $Henkinized(Model(M))_T nvDash forall x. phi(x)$ であることを示せばよい．

      $forall x. phi(x) in.not T^*$ なら1階述語論理の計算によって $exists x. not phi(x) in T^*$ である．
      特に $x$ を最初に固定した $v_0$ として $exists v_0. not phi(v_0) in T^*$ である．

      $T^*$ は $not phi$ に対するHenkin公理 $eta_(not phi) equiv exists v_0. not phi(v_0) -> not phi(c_(not phi))$ を含むので，$not phi(c_(not phi)) in T^*$ である．したがって，$phi(c_(not phi)) in.not T^*$ である．

      帰納法の仮定より，$Henkinized(Model(M))_T nvDash phi(c_(not phi))$ である．したがって，$Henkinized(Model(M))_T nvDash forall x. phi(x)$ である．
    ]
  ]
]

#corollary[
  $Henkinized(Model(M))_T vDash T$．
]<cor:T_has_model>
#proof[
  $Henkinized(Model(M))_T$ が $T^*$ のモデルであることと，$T subset.eq T^*$ から従う．
]

@cor:T_has_model より，@thm:generalized_completeness が示せる．

#proof[@thm:generalized_completeness][
  片方は@lem:generalized_soundness そのもの．
  もう片方は無矛盾な理論から $T$ のHenkinモデル $Henkinized(Model(M))_T$ を構成すれば，@cor:T_has_model より $T$ のモデルとなるので良い．
]
