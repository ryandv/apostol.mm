$[ set.mm $]

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Ryan DV
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Solutions to exercises given in Calculus, Vol. 1 by Apostol, 2nd ed.

  When possible, proofs depend only on theorems of first-order logic,
  the field axioms as given by Apostol, prior results, and some basic
  closure and membership theorems for the real numbers (which appear
  to be implicitly assumed through the text).

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Preliminaries
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  We now present "proofs" of the field axioms as given by Apostol, but
  derived from other Metamath theorems over the complex numbers.

$)

${
  axapostoladd1 $p |- ( ( A e. RR /\ B e. RR ) -> ( A + B ) = ( B + A ) ) $=
    cA cr wcel cB cr wcel wa cA cc wcel cB cc wcel wa cA cB caddc co cB cA
    caddc co wceq cA cr wcel cA cc wcel cB cr wcel cB cc wcel cA recn cB recn
    anim12i cA cB addcom syl $.
$}

${
  axapostolmul1 $p |- ( ( A e. RR /\ B e. RR ) -> ( A x. B ) = ( B x. A ) ) $=
    cA cr wcel cB cr wcel wa cA cc wcel cB cc wcel wa cA cB cmul co cB cA cmul
    co wceq cA cr wcel cA cc wcel cB cr wcel cB cc wcel cA recn cB recn anim12i
    cA cB mulcom syl $.
$}

${
  axapostoladd2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A + ( B + C ) ) = ( ( A + B ) + C ) ) $=
    cA cr wcel cB cr wcel cC cr wcel w3a cA cB caddc co cC caddc co cA cB cC
    caddc co caddc co cA cr wcel cB cr wcel cC cr wcel w3a cA cc wcel cB cc
    wcel cC cc wcel w3a cA cB caddc co cC caddc co cA cB cC caddc co caddc co
    wceq cA cr wcel cA cc wcel cB cr wcel cB cc wcel cC cr wcel cC cc wcel cA
    recn cB recn cC recn 3anim123i cA cB cC addass syl eqcomd $.
$}

${
  axapostolmul2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A x. ( B x. C ) ) = ( ( A x. B ) x. C ) ) $=
    cA cr wcel cB cr wcel cC cr wcel w3a cA cB cmul co cC cmul co cA cB cC cmul
    co cmul co cA cr wcel cB cr wcel cC cr wcel w3a cA cc wcel cB cc wcel cC cc
    wcel w3a cA cB cmul co cC cmul co cA cB cC cmul co cmul co wceq cA cr wcel
    cA cc wcel cB cr wcel cB cc wcel cC cr wcel cC cc wcel cA recn cB recn cC
    recn 3anim123i cA cB cC mulass syl eqcomd $.
$}

${
  axaspotol3 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A x. ( B + C ) ) = ( ( A x. B ) + ( A x. C ) ) ) $=
    cA cr wcel cB cr wcel cC cr wcel w3a cA cc wcel cB cc wcel cC cc wcel w3a
    cA cB cC caddc co cmul co cA cB cmul co cA cC cmul co caddc co wceq cA cr
    wcel cA cc wcel cB cr wcel cB cc wcel cC cr wcel cC cc wcel cA recn cB recn
    cC recn 3anim123i cA cB cC adddi syl $.
$}

${
  axapostoladd4 $p |- ( A e. RR -> ( A + 0 ) = A ) $=
    cA cr wcel cA cc wcel cA cc0 caddc co cA wceq cA recn cA addid1 syl $.
$}

${
  axapostolmul4 $p |- ( A e. RR -> ( 1 x. A ) = A ) $=
    cA cr wcel cA cc wcel c1 cA cmul co cA wceq cA recn cA mulid2 syl $.
$}

${
  $d x A $.
  axapostol5 $p |- ( A e. RR -> E. x e. RR ( A + x ) = 0 ) $=
    vx cA ax-rnegex $.
$}

${
  $d x A $.
  axapostol6 $p |- ( ( A e. RR /\ A =/= 0 ) -> E. x e. RR ( A x. x ) = 1 ) $=
    vx cA ax-rrecex $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Field Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The above justifications by existing Metamath theorems of the field axioms
  as given by Apostol, p.18 are now restated as Metamath axioms.

$)

${
  ax-apostoladd1 $a |- ( ( A e. RR /\ B e. RR ) -> ( A + B ) = ( B + A ) ) $.
  ax-apostolmul1 $a |- ( ( A e. RR /\ B e. RR ) -> ( A x. B ) = ( B x. A ) ) $.
  ax-apostoladd2 $a |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A + ( B + C ) ) = ( ( A + B ) + C ) ) $.
  ax-apostolmul2 $a |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A x. ( B x. C ) ) = ( ( A x. B ) x. C ) ) $.
  ax-apostol3 $a |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A x. ( B + C ) ) = ( ( A x. B ) + ( A x. C ) ) ) $.
  ax-apostoladd4 $a |- ( A e. RR -> ( A + 0 ) = A ) $.
  ax-apostolmul4 $a |- ( A e. RR -> ( 1 x. A ) = A ) $.
  ax-apostol5 $a |- ( A e. RR -> E. x e. RR ( A + x ) = 0 ) $.
  ax-apostol6 $a |- ( ( A e. RR /\ A =/= 0 ) -> E. x e. RR ( A x. x ) = 1 ) $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                I 3.3 Exercises
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Proofs of Theorems I.1 - I.15 follow.

$)

${
  $d x A $. $d x B $. $d x C $.
  apostoli.1 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A + B ) = ( A + C ) <-> B = C ) ) $=
    cA cr wcel cB cr wcel cC cr wcel w3a cA cB caddc co cA cC caddc co wceq cB
    cC wceq cA cr wcel cB cr wcel cC cr wcel w3a cA vx cv caddc co cc0 wceq cA
    cB caddc co cA cC caddc co wceq cB cC wceq wi vx cr cA cr wcel cB cr wcel
    cC cr wcel w3a cA cr wcel cA vx cv caddc co cc0 wceq vx cr wrex cA cr wcel
    cB cr wcel cC cr wcel simp1 vx cA ax-apostol5 syl cA cr wcel cB cr wcel cC
    cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa cA cB caddc co
    cA cC caddc co wceq cB cC wceq cA cr wcel cB cr wcel cC cr wcel w3a vx cv
    cr wcel cA vx cv caddc co cc0 wceq wa wa cA cB caddc co cA cC caddc co wceq
    wa cB vx cv cA cC caddc co caddc co cC cA cr wcel cB cr wcel cC cr wcel w3a
    vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa cA cB caddc co cA cC caddc
    co wceq wa vx cv cA cB caddc co caddc co cB vx cv cA cC caddc co caddc co
    cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0
    wceq wa wa cA cB caddc co cA cC caddc co wceq wa cA cr wcel cB cr wcel cC
    cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa vx cv cA cB
    caddc co caddc co cB wceq cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr
    wcel cA vx cv caddc co cc0 wceq wa wa cA cB caddc co cA cC caddc co wceq
    simpl cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co
    cc0 wceq wa wa vx cv cA cB caddc co caddc co vx cv cA caddc co cB caddc co
    cc0 cB caddc co cB cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx
    cv caddc co cc0 wceq wa wa vx cv cr wcel cA cr wcel cB cr wcel vx cv cA cB
    caddc co caddc co vx cv cA caddc co cB caddc co wceq cA cr wcel cB cr wcel
    cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq simprl cA cr wcel
    cB cr wcel cC cr wcel vx cv cr wcel cA vx cv caddc co cc0 wceq wa simpl1 cA
    cr wcel cB cr wcel cC cr wcel vx cv cr wcel cA vx cv caddc co cc0 wceq wa
    simpl2 vx cv cA cB ax-apostoladd2 syl3anc cA cr wcel cB cr wcel cC cr wcel
    w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa vx cv cA caddc co cc0 cB
    caddc cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co
    cc0 wceq wa wa cA vx cv caddc co vx cv cA caddc co cc0 cA cr wcel cB cr
    wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa cA cr
    wcel vx cv cr wcel cA vx cv caddc co vx cv cA caddc co wceq cA cr wcel cB
    cr wcel cC cr wcel vx cv cr wcel cA vx cv caddc co cc0 wceq wa simpl1 cA cr
    wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq
    simprl cA vx cv ax-apostoladd1 syl2anc cA cr wcel cB cr wcel cC cr wcel w3a
    vx cv cr wcel cA vx cv caddc co cc0 wceq simprr eqtr3d oveq1d cA cr wcel cB
    cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa cB cr
    wcel cc0 cB caddc co cB wceq cA cr wcel cB cr wcel cC cr wcel vx cv cr wcel
    cA vx cv caddc co cc0 wceq wa simpl2 cB cr wcel cB cc0 caddc co cc0 cB
    caddc co cB cB cr wcel cc0 cr wcel cB cc0 caddc co cc0 cB caddc co wceq 0re
    cB cc0 ax-apostoladd1 mpan2 cB ax-apostoladd4 eqtr3d syl 3eqtrd syl cA cB
    caddc co cA cC caddc co wceq vx cv cA cB caddc co caddc co vx cv cA cC
    caddc co caddc co wceq cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel
    cA vx cv caddc co cc0 wceq wa wa cA cB caddc co cA cC caddc co vx cv caddc
    oveq2 adantl eqtr3d cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA
    vx cv caddc co cc0 wceq wa wa cA cB caddc co cA cC caddc co wceq wa cA cr
    wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa
    wa vx cv cA cC caddc co caddc co cC wceq cA cr wcel cB cr wcel cC cr wcel
    w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa cA cB caddc co cA cC
    caddc co wceq simpl cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA
    vx cv caddc co cc0 wceq wa wa vx cv cA cC caddc co caddc co vx cv cA caddc
    co cC caddc co cc0 cC caddc co cC cA cr wcel cB cr wcel cC cr wcel w3a vx
    cv cr wcel cA vx cv caddc co cc0 wceq wa wa vx cv cr wcel cA cr wcel cC cr
    wcel vx cv cA cC caddc co caddc co vx cv cA caddc co cC caddc co wceq cA cr
    wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq
    simprl cA cr wcel cB cr wcel cC cr wcel vx cv cr wcel cA vx cv caddc co cc0
    wceq wa simpl1 cA cr wcel cB cr wcel cC cr wcel vx cv cr wcel cA vx cv
    caddc co cc0 wceq wa simpl3 vx cv cA cC ax-apostoladd2 syl3anc cA cr wcel
    cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq wa wa vx
    cv cA caddc co cc0 cC caddc cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr
    wcel cA vx cv caddc co cc0 wceq wa wa cA vx cv caddc co vx cv cA caddc co
    cc0 cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co
    cc0 wceq wa wa cA cr wcel vx cv cr wcel cA vx cv caddc co vx cv cA caddc co
    wceq cA cr wcel cB cr wcel cC cr wcel vx cv cr wcel cA vx cv caddc co cc0
    wceq wa simpl1 cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv
    caddc co cc0 wceq simprl cA vx cv ax-apostoladd1 syl2anc cA cr wcel cB cr
    wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co cc0 wceq simprr eqtr3d
    oveq1d cA cr wcel cB cr wcel cC cr wcel w3a vx cv cr wcel cA vx cv caddc co
    cc0 wceq wa wa cC cr wcel cc0 cC caddc co cC wceq cA cr wcel cB cr wcel cC
    cr wcel vx cv cr wcel cA vx cv caddc co cc0 wceq wa simpl3 cC cr wcel cC
    cc0 caddc co cc0 cC caddc co cC cC cr wcel cc0 cr wcel cC cc0 caddc co cc0
    cC caddc co wceq 0re cC cc0 ax-apostoladd1 mpan2 cC ax-apostoladd4 eqtr3d
    syl 3eqtrd syl eqtrd ex rexlimddv cB cC wceq cA cB caddc co cA cC caddc co
    wceq wi cA cr wcel cB cr wcel cC cr wcel w3a cB cC cA caddc oveq2 a1i
    impbid $.
$}

${
  $d x y $.
  $d x A $. $d x B $. $d x C $.
  $d y A $. $d y B $. $d y C $.

  apostoli.2 $p |- ( ( A e. RR /\ B e. RR ) -> E! x e. RR ( A + x ) = B ) $=
    cA cr wcel cB cr wcel wa cA vy cv caddc co cc0 wceq cA vx cv caddc co cB
    wceq vx cr wreu vy cr cA cr wcel cA vy cv caddc co cc0 wceq vy cr wrex cB
    cr wcel vy cA ax-apostol5 adantr cA cr wcel cB cr wcel wa vy cv cr wcel cA
    vy cv caddc co cc0 wceq wa wa vy cv cB caddc co cr wcel cA vx cv caddc co
    cB wceq vx cv vy cv cB caddc co wceq wb vx cr wral cA vx cv caddc co cB
    wceq vx cr wreu cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co
    cc0 wceq wa wa vy cv cB cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv
    caddc co cc0 wceq simprl cA cr wcel cB cr wcel vy cv cr wcel cA vy cv caddc
    co cc0 wceq wa simplr readdcld cA cr wcel cB cr wcel wa vy cv cr wcel cA vy
    cv caddc co cc0 wceq wa wa cA vx cv caddc co cB wceq vx cv vy cv cB caddc
    co wceq wb vx cr cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co
    cc0 wceq wa wa vx cv cr wcel wa vy cv cA vx cv caddc co caddc co vy cv cB
    caddc co wceq cA vx cv caddc co cB wceq vx cv vy cv cB caddc co wceq cA cr
    wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr
    wcel wa vy cv cr wcel cA vx cv caddc co cr wcel cB cr wcel vy cv cA vx cv
    caddc co caddc co vy cv cB caddc co wceq cA vx cv caddc co cB wceq wb cA cr
    wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq vx cv cr wcel
    simplrl cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq
    wa wa vx cv cr wcel wa cA vx cv cA cr wcel cB cr wcel vy cv cr wcel cA vy
    cv caddc co cc0 wceq wa vx cv cr wcel simplll cA cr wcel cB cr wcel wa vy
    cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel simpr readdcld cA
    cr wcel cB cr wcel vy cv cr wcel cA vy cv caddc co cc0 wceq wa vx cv cr
    wcel simpllr vy cv cA vx cv caddc co cB apostoli.1 syl3anc cA cr wcel cB cr
    wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa vy
    cv cA vx cv caddc co caddc co vx cv vy cv cB caddc co cA cr wcel cB cr wcel
    wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa vy cv cA
    vx cv caddc co caddc co vy cv cA caddc co vx cv caddc co vx cv cA cr wcel
    cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel
    wa vy cv cr wcel cA cr wcel vx cv cr wcel vy cv cA vx cv caddc co caddc co
    vy cv cA caddc co vx cv caddc co wceq cA cr wcel cB cr wcel wa vy cv cr
    wcel cA vy cv caddc co cc0 wceq vx cv cr wcel simplrl cA cr wcel cB cr wcel
    vy cv cr wcel cA vy cv caddc co cc0 wceq wa vx cv cr wcel simplll cA cr
    wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr
    wcel simpr vy cv cA vx cv ax-apostoladd2 syl3anc cA cr wcel cB cr wcel wa
    vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa vx cv vy cv
    cA caddc co caddc co vx cv cc0 caddc co vy cv cA caddc co vx cv caddc co vx
    cv cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa
    vx cv cr wcel wa vx cv vy cv cA caddc co caddc co vx cv cc0 caddc co wceq
    vy cv cA caddc co cc0 wceq cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv
    caddc co cc0 wceq wa wa vx cv cr wcel wa cA vy cv caddc co vy cv cA caddc
    co cc0 cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa
    wa vx cv cr wcel wa cA cr wcel vy cv cr wcel cA vy cv caddc co vy cv cA
    caddc co wceq cA cr wcel cB cr wcel vy cv cr wcel cA vy cv caddc co cc0
    wceq wa vx cv cr wcel simplll cA cr wcel cB cr wcel wa vy cv cr wcel cA vy
    cv caddc co cc0 wceq vx cv cr wcel simplrl cA vy cv ax-apostoladd1 syl2anc
    cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq vx cv cr
    wcel simplrr eqtr3d cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc
    co cc0 wceq wa wa vx cv cr wcel wa vx cv cr wcel vy cv cA caddc co cr wcel
    cc0 cr wcel vx cv vy cv cA caddc co caddc co vx cv cc0 caddc co wceq vy cv
    cA caddc co cc0 wceq wb cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv
    caddc co cc0 wceq wa wa vx cv cr wcel simpr cA cr wcel cB cr wcel wa vy cv
    cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa vy cv cA cA cr
    wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq vx cv cr wcel
    simplrl cA cr wcel cB cr wcel vy cv cr wcel cA vy cv caddc co cc0 wceq wa
    vx cv cr wcel simplll readdcld cc0 cr wcel cA cr wcel cB cr wcel wa vy cv
    cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa 0re a1i vx cv vy
    cv cA caddc co cc0 apostoli.1 syl3anc mpbird cA cr wcel cB cr wcel wa vy cv
    cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa vx cv cr wcel vy
    cv cA caddc co cr wcel vx cv vy cv cA caddc co caddc co vy cv cA caddc co
    vx cv caddc co wceq cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc
    co cc0 wceq wa wa vx cv cr wcel simpr cA cr wcel cB cr wcel wa vy cv cr
    wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr wcel wa vy cv cA cA cr wcel
    cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq vx cv cr wcel
    simplrl cA cr wcel cB cr wcel vy cv cr wcel cA vy cv caddc co cc0 wceq wa
    vx cv cr wcel simplll readdcld vx cv vy cv cA caddc co ax-apostoladd1
    syl2anc cA cr wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq
    wa wa vx cv cr wcel wa vx cv cr wcel vx cv cc0 caddc co vx cv wceq cA cr
    wcel cB cr wcel wa vy cv cr wcel cA vy cv caddc co cc0 wceq wa wa vx cv cr
    wcel simpr vx cv ax-apostoladd4 syl 3eqtr3d eqtrd eqeq1d bitr3d ralrimiva
    cA vx cv caddc co cB wceq vx cr vy cv cB caddc co reu6i syl2anc rexlimddv
    $.
$}

${
  $d x A $. $d x B $.
  resubval $p |- ( ( A e. RR /\ B e. RR ) -> ( A - B ) = ( iota_ x e. RR ( B + x ) = A ) ) $=
    cA cr wcel cB cr wcel wa cA cB cmin co cB vx cv caddc co cA wceq vx cc crio
    cB vx cv caddc co cA wceq vx cr crio cA cr wcel cA cc wcel cB cc wcel cA cB
    cmin co cB vx cv caddc co cA wceq vx cc crio wceq cB cr wcel cr cc wss cA
    cr wcel cA cc wcel wi ax-resscn cr cc cA ssel ax-mp cr cc wss cB cr wcel cB
    cc wcel wi ax-resscn cr cc cB ssel ax-mp vx cA cB subval syl2an cA cr wcel
    cB cr wcel wa cr cc wss cB vx cv caddc co cA wceq vx cr wrex cB vx cv caddc
    co cA wceq vx cc wreu w3a cB vx cv caddc co cA wceq vx cr crio cB vx cv
    caddc co cA wceq vx cc crio wceq cA cr wcel cB cr wcel wa cr cc wss cB vx
    cv caddc co cA wceq vx cr wrex cB vx cv caddc co cA wceq vx cc wreu cr cc
    wss cA cr wcel cB cr wcel wa ax-resscn a1i cA cr wcel cB cr wcel wa cB cr
    wcel cA cr wcel wa cB vx cv caddc co cA wceq vx cr wreu cB vx cv caddc co
    cA wceq vx cr wrex cA cr wcel cB cr wcel pm3.22 vx cB cA apostoli.2 cB vx
    cv caddc co cA wceq vx cr reurex 3syl cB cr wcel cA cr wcel cB vx cv caddc
    co cA wceq vx cc wreu cB cr wcel cB cc wcel cA cc wcel cB vx cv caddc co cA
    wceq vx cc wreu cA cr wcel cr cc wss cB cr wcel cB cc wcel wi ax-resscn cr
    cc cB ssel ax-mp cr cc wss cA cr wcel cA cc wcel wi ax-resscn cr cc cA ssel
    ax-mp vx cB cA negeu syl2an ancoms 3jca cB vx cv caddc co cA wceq vx cr cc
    riotass syl eqtr4d $.
$}

${
  $d x A $.

  renegid $p |- ( A e. RR -> ( A + -u A ) = 0 ) $=
    cA cr wcel cA cA cneg caddc co cc0 wceq cA vx cv caddc co cc0 wceq vx cr
    crio cA cneg wceq cA cr wcel cA cneg cc0 cA cmin co cA vx cv caddc co cc0
    wceq vx cr crio cA df-neg cc0 cr wcel cA cr wcel cc0 cA cmin co cA vx cv
    caddc co cc0 wceq vx cr crio wceq 0re vx cc0 cA resubval mpan syl5req cA cr
    wcel cA cneg cr wcel cA vx cv caddc co cc0 wceq vx cr wreu cA cA cneg caddc
    co cc0 wceq cA vx cv caddc co cc0 wceq vx cr crio cA cneg wceq wb cA
    renegcl cA cr wcel cc0 cr wcel cA vx cv caddc co cc0 wceq vx cr wreu 0re vx
    cA cc0 apostoli.2 mpan2 cA vx cv caddc co cc0 wceq cA cA cneg caddc co cc0
    wceq vx cr cA cneg vx cv cA cneg wceq cA vx cv caddc co cA cA cneg caddc co
    cc0 vx cv cA cneg cA caddc oveq2 eqeq1d riota2 syl2anc mpbird $.
$}

${
  $d x A $. $d x B $.

  apostoli.3 $p |- ( ( A e. RR /\ B e. RR ) -> ( A + -u B ) = ( A - B ) ) $=
    cA cr wcel cB cr wcel wa cA cB cneg caddc co cB cneg cA caddc co cA cB cmin
    co cB cr wcel cA cr wcel cB cneg cr wcel cA cB cneg caddc co cB cneg cA
    caddc co wceq cB renegcl cA cB cneg ax-apostoladd1 sylan2 cA cr wcel cB cr
    wcel wa cB cB cneg cA caddc co caddc co cB cA cB cmin co caddc co wceq cB
    cneg cA caddc co cA cB cmin co wceq cA cr wcel cB cr wcel wa cB cB cneg cA
    caddc co caddc co cA cB cA cB cmin co caddc co cA cr wcel cB cr wcel wa cB
    cB cneg cA caddc co caddc co cB cB cneg caddc co cA caddc co cA cB cr wcel
    cA cr wcel cB cB cneg cA caddc co caddc co cB cB cneg caddc co cA caddc co
    wceq cB cr wcel cA cr wcel cB cB cneg cA caddc co caddc co cB cB cneg caddc
    co cA caddc co wceq cB cr wcel cB cr wcel cB cneg cr wcel cA cr wcel cB cB
    cneg cA caddc co caddc co cB cB cneg caddc co cA caddc co wceq cB renegcl
    cB cB cneg cA ax-apostoladd2 syl3an2 3anidm12 ancoms cA cr wcel cB cr wcel
    wa cB cB cneg caddc co cA caddc co cc0 cA caddc co cA cB cr wcel cB cB cneg
    caddc co cA caddc co cc0 cA caddc co wceq cA cr wcel cB cr wcel cB cB cneg
    caddc co cc0 cA caddc cB renegid oveq1d adantl cA cr wcel cc0 cA caddc co
    cA wceq cB cr wcel cA cr wcel cc0 cA caddc co cA cc0 caddc co cA cc0 cr
    wcel cA cr wcel cc0 cA caddc co cA cc0 caddc co wceq 0re cc0 cA
    ax-apostoladd1 mpan cA ax-apostoladd4 eqtrd adantr eqtrd eqtrd cA cr wcel
    cB cr wcel wa cB cA cB cmin co caddc co cA wceq cB vx cv caddc co cA wceq
    vx cr crio cA cB cmin co wceq cA cr wcel cB cr wcel wa cA cB cmin co cB vx
    cv caddc co cA wceq vx cr crio vx cA cB resubval eqcomd cA cr wcel cB cr
    wcel wa cA cB cmin co cr wcel cB vx cv caddc co cA wceq vx cr wreu cB cA cB
    cmin co caddc co cA wceq cB vx cv caddc co cA wceq vx cr crio cA cB cmin co
    wceq wb cA cB resubcl cB cr wcel cA cr wcel cB vx cv caddc co cA wceq vx cr
    wreu vx cB cA apostoli.2 ancoms cB vx cv caddc co cA wceq cB cA cB cmin co
    caddc co cA wceq vx cr cA cB cmin co vx cv cA cB cmin co wceq cB vx cv
    caddc co cB cA cB cmin co caddc co cA vx cv cA cB cmin co cB caddc oveq2
    eqeq1d riota2 syl2anc mpbird eqtr4d cA cr wcel cB cr wcel wa cB cr wcel cB
    cneg cA caddc co cr wcel cA cB cmin co cr wcel cB cB cneg cA caddc co caddc
    co cB cA cB cmin co caddc co wceq cB cneg cA caddc co cA cB cmin co wceq wb
    cA cr wcel cB cr wcel simpr cA cr wcel cB cr wcel wa cB cneg cA cA cr wcel
    cB cr wcel wa cB cr wcel cB cneg cr wcel cA cr wcel cB cr wcel simpr cB
    renegcl syl cA cr wcel cB cr wcel simpl readdcld cA cB resubcl cB cB cneg
    cA caddc co cA cB cmin co apostoli.1 syl3anc mpbid eqtrd $.
$}

${
  apostoli.4 $p |- ( A e. RR -> -u -u A = A ) $=
    cA cr wcel cA cneg cA cneg cneg caddc co cA cneg cA caddc co wceq cA cneg
    cneg cA wceq cA cr wcel cA cneg cA cneg cneg caddc co cc0 cA cA cneg caddc
    co cA cneg cA caddc co cA cr wcel cA cneg cr wcel cA cneg cA cneg cneg
    caddc co cc0 wceq cA renegcl cA cneg renegid syl cA renegid cA cr wcel cA
    cr wcel cA cr wcel wa cA cA cneg caddc co cA cneg cA caddc co wceq cA cr
    wcel pm4.24 cA cr wcel cA cr wcel cA cneg cr wcel cA cA cneg caddc co cA
    cneg cA caddc co wceq cA renegcl cA cA cneg ax-apostoladd1 sylan2 sylbi
    3eqtr2d cA cr wcel cA cneg cr wcel cA cneg cneg cr wcel cA cr wcel cA cneg
    cA cneg cneg caddc co cA cneg cA caddc co wceq cA cneg cneg cA wceq wb cA
    renegcl cA cr wcel cA cneg cA renegcl renegcld cA cr wcel id cA cneg cA
    cneg cneg cA apostoli.1 syl3anc mpbid $.
$}

${
  $d x A $. $d x B $. $d x C $.

  apostoli.5 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A x. ( B - C ) ) = ( ( A x. B ) - ( A x. C ) ) ) $=
    cA cr wcel cB cr wcel cC cr wcel w3a cA cB cmul co cA cC cmul co cmin co cA
    cB cC cmin co cmul co cA cr wcel cB cr wcel cC cr wcel w3a cA cC cmul co cA
    cB cC cmin co cmul co caddc co cA cB cmul co wceq cA cB cmul co cA cC cmul
    co cmin co cA cB cC cmin co cmul co wceq cA cr wcel cB cr wcel cC cr wcel
    w3a cA cC cB cC cmin co caddc co cmul co cA cC cmul co cA cB cC cmin co
    cmul co caddc co cA cB cmul co cA cr wcel cB cr wcel cC cr wcel w3a cA cr
    wcel cC cr wcel cB cC cmin co cr wcel cA cC cB cC cmin co caddc co cmul co
    cA cC cmul co cA cB cC cmin co cmul co caddc co wceq cA cr wcel cB cr wcel
    cC cr wcel simp1 cA cr wcel cB cr wcel cC cr wcel simp3 cA cr wcel cB cr
    wcel cC cr wcel w3a cB cC cA cr wcel cB cr wcel cC cr wcel simp2 cA cr wcel
    cB cr wcel cC cr wcel simp3 resubcld cA cC cB cC cmin co ax-apostol3
    syl3anc cB cr wcel cC cr wcel cA cC cB cC cmin co caddc co cmul co cA cB
    cmul co wceq cA cr wcel cB cr wcel cC cr wcel wa cC cB cC cmin co caddc co
    cB cA cmul cB cr wcel cC cr wcel wa cC cB cC cneg caddc co caddc co cC cB
    cC cmin co caddc co cB cB cr wcel cC cr wcel wa cB cC cneg caddc co cB cC
    cmin co cC caddc cB cC apostoli.3 oveq2d cB cr wcel cC cr wcel wa cC cC
    cneg cB caddc co caddc co cC cC cneg caddc co cB caddc co cC cB cC cneg
    caddc co caddc co cB cC cr wcel cB cr wcel cC cC cneg cB caddc co caddc co
    cC cC cneg caddc co cB caddc co wceq cC cr wcel cB cr wcel cC cC cneg cB
    caddc co caddc co cC cC cneg caddc co cB caddc co wceq cC cr wcel cC cr
    wcel cC cneg cr wcel cB cr wcel cC cC cneg cB caddc co caddc co cC cC cneg
    caddc co cB caddc co wceq cC renegcl cC cC cneg cB ax-apostoladd2 syl3an2
    3anidm12 ancoms cC cr wcel cB cr wcel cC cC cneg cB caddc co caddc co cC cB
    cC cneg caddc co caddc co wceq cC cr wcel cC cneg cr wcel cB cr wcel cC cC
    cneg cB caddc co caddc co cC cB cC cneg caddc co caddc co wceq cC renegcl
    cC cneg cr wcel cB cr wcel wa cC cneg cB caddc co cB cC cneg caddc co cC
    caddc cC cneg cB ax-apostoladd1 oveq2d sylan ancoms cB cr wcel cC cr wcel
    wa cC cC cneg caddc co cB caddc co cc0 cB caddc co cB cc0 caddc co cB cC cr
    wcel cC cC cneg caddc co cB caddc co cc0 cB caddc co wceq cB cr wcel cC cr
    wcel cC cC cneg caddc co cc0 cB caddc cC renegid oveq1d adantl cB cr wcel
    cc0 cB caddc co cB cc0 caddc co wceq cC cr wcel cc0 cr wcel cB cr wcel cc0
    cB caddc co cB cc0 caddc co wceq 0re cc0 cB ax-apostoladd1 mpan adantr cB
    cr wcel cB cc0 caddc co cB wceq cC cr wcel cB ax-apostoladd4 adantr 3eqtrd
    3eqtr3d eqtr3d oveq2d 3adant1 eqtr3d cA cr wcel cB cr wcel cC cr wcel w3a
    cA cC cmul co cA cB cC cmin co cmul co caddc co cA cB cmul co wceq cA cC
    cmul co vx cv caddc co cA cB cmul co wceq vx cr crio cA cB cC cmin co cmul
    co wceq cA cB cmul co cA cC cmul co cmin co cA cB cC cmin co cmul co wceq
    cA cr wcel cB cr wcel cC cr wcel w3a cA cB cC cmin co cmul co cr wcel cA cC
    cmul co vx cv caddc co cA cB cmul co wceq vx cr wreu cA cC cmul co cA cB cC
    cmin co cmul co caddc co cA cB cmul co wceq cA cC cmul co vx cv caddc co cA
    cB cmul co wceq vx cr crio cA cB cC cmin co cmul co wceq wb cA cr wcel cB
    cr wcel cC cr wcel w3a cA cB cC cmin co cA cr wcel cB cr wcel cC cr wcel
    simp1 cA cr wcel cB cr wcel cC cr wcel w3a cB cC cA cr wcel cB cr wcel cC
    cr wcel simp2 cA cr wcel cB cr wcel cC cr wcel simp3 resubcld remulcld cA
    cr wcel cB cr wcel cC cr wcel w3a cA cC cmul co cr wcel cA cB cmul co cr
    wcel cA cC cmul co vx cv caddc co cA cB cmul co wceq vx cr wreu cA cr wcel
    cB cr wcel cC cr wcel w3a cA cC cA cr wcel cB cr wcel cC cr wcel simp1 cA
    cr wcel cB cr wcel cC cr wcel simp3 remulcld cA cr wcel cB cr wcel cC cr
    wcel w3a cA cB cA cr wcel cB cr wcel cC cr wcel simp1 cA cr wcel cB cr wcel
    cC cr wcel simp2 remulcld vx cA cC cmul co cA cB cmul co apostoli.2 syl2anc
    cA cC cmul co vx cv caddc co cA cB cmul co wceq cA cC cmul co cA cB cC cmin
    co cmul co caddc co cA cB cmul co wceq vx cr cA cB cC cmin co cmul co vx cv
    cA cB cC cmin co cmul co wceq cA cC cmul co vx cv caddc co cA cC cmul co cA
    cB cC cmin co cmul co caddc co cA cB cmul co vx cv cA cB cC cmin co cmul co
    cA cC cmul co caddc oveq2 eqeq1d riota2 syl2anc cA cr wcel cB cr wcel cC cr
    wcel w3a cA cC cmul co vx cv caddc co cA cB cmul co wceq vx cr crio cA cB
    cmul co cA cC cmul co cmin co cA cB cC cmin co cmul co cA cr wcel cB cr
    wcel cC cr wcel w3a cA cB cmul co cA cC cmul co cmin co cA cC cmul co vx cv
    caddc co cA cB cmul co wceq vx cr crio cA cr wcel cB cr wcel cC cr wcel w3a
    cA cB cmul co cr wcel cA cC cmul co cr wcel cA cB cmul co cA cC cmul co
    cmin co cA cC cmul co vx cv caddc co cA cB cmul co wceq vx cr crio wceq cA
    cr wcel cB cr wcel cC cr wcel w3a cA cB cA cr wcel cB cr wcel cC cr wcel
    simp1 cA cr wcel cB cr wcel cC cr wcel simp2 remulcld cA cr wcel cB cr wcel
    cC cr wcel w3a cA cC cA cr wcel cB cr wcel cC cr wcel simp1 cA cr wcel cB
    cr wcel cC cr wcel simp3 remulcld vx cA cB cmul co cA cC cmul co resubval
    syl2anc eqcomd eqeq1d bitrd mpbid eqcomd $.
$}

${
  apostoli.6 $p |- ( A e. RR -> ( A x. 0 ) = 0 ) $=
    cA cr wcel cA cc0 cmul co cA cc0 cmul co caddc co cA cc0 cmul co cc0 caddc
    co wceq cA cc0 cmul co cc0 wceq cA cr wcel cA cc0 cmul co cA cc0 cmul co
    caddc co cA cc0 cmul co cA cc0 cmul co cc0 caddc co cA cr wcel cA cc0 cmul
    co cA cc0 cc0 caddc co cmul co cA cc0 cmul co cA cc0 cmul co caddc co cc0
    cr wcel cA cc0 cc0 caddc co cmul co cA cc0 cmul co wceq 0re cc0 cr wcel cc0
    cc0 caddc co cc0 cA cmul cc0 ax-apostoladd4 oveq2d ax-mp cA cr wcel cc0 cr
    wcel cc0 cr wcel cA cc0 cc0 caddc co cmul co cA cc0 cmul co cA cc0 cmul co
    caddc co wceq 0re 0re cA cc0 cc0 ax-apostol3 mp3an23 syl5reqr cA cr wcel cA
    cc0 cmul co cr wcel cA cc0 cmul co cc0 caddc co cA cc0 cmul co wceq cA cr
    wcel cc0 cr wcel cA cc0 cmul co cr wcel 0re cA cc0 remulcl mpan2 cA cc0
    cmul co ax-apostoladd4 syl eqtr4d cA cr wcel cA cc0 cmul co cr wcel cA cc0
    cmul co cr wcel cA cc0 cmul co cA cc0 cmul co caddc co cA cc0 cmul co cc0
    caddc co wceq cA cc0 cmul co cc0 wceq wb cA cr wcel cc0 cr wcel cA cc0 cmul
    co cr wcel 0re cA cc0 remulcl mpan2 cA cr wcel cc0 cr wcel cA cc0 cmul co
    cr wcel 0re cA cc0 remulcl mpan2 cA cc0 cmul co cr wcel cA cc0 cmul co cr
    wcel cc0 cr wcel cA cc0 cmul co cA cc0 cmul co caddc co cA cc0 cmul co cc0
    caddc co wceq cA cc0 cmul co cc0 wceq wb 0re cA cc0 cmul co cA cc0 cmul co
    cc0 apostoli.1 mp3an3 syl2anc mpbid $.
$}

${
  $d x A $. $d x B $. $d x C $.

  apostoli.7 $p |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ C =/= 0 ) ) -> ( ( C x. A ) = ( C x. B ) <-> A = B ) ) $=
    cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a cC cA cmul co cC cB cmul
    co wceq cA cB wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a cC vx
    cv cmul co c1 wceq cC cA cmul co cC cB cmul co wceq cA cB wceq wi vx cr cC
    cr wcel cC cc0 wne wa cA cr wcel cC vx cv cmul co c1 wceq vx cr wrex cB cr
    wcel vx cC ax-apostol6 3ad2ant3 cA cr wcel cB cr wcel cC cr wcel cC cc0 wne
    wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa cC cA cmul co cC cB
    cmul co wceq cA cB wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a
    vx cv cr wcel cC vx cv cmul co c1 wceq wa wa cC cA cmul co cC cB cmul co
    wceq wa vx cv cC cB cmul co cmul co cA cB cA cr wcel cB cr wcel cC cr wcel
    cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa cC cA cmul
    co cC cB cmul co wceq wa vx cv cC cA cmul co cmul co cA wceq vx cv cC cB
    cmul co cmul co cA wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a
    vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv cC cA cmul co cmul co cA
    wceq cC cA cmul co cC cB cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC
    cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv cC cA
    cmul co cmul co vx cv cC cmul co cA cmul co cA cA cr wcel cB cr wcel cC cr
    wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv
    cr wcel cC cr wcel cA cr wcel vx cv cC cA cmul co cmul co vx cv cC cmul co
    cA cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr
    wcel cC vx cv cmul co c1 wceq simprl cC cr wcel cC cc0 wne cA cr wcel cB cr
    wcel vx cv cr wcel cC vx cv cmul co c1 wceq wa simpl3l cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa vx cv cr wcel cC vx cv cmul co c1 wceq wa
    simpl1 vx cv cC cA ax-apostolmul2 syl3anc cA cr wcel cB cr wcel cC cr wcel
    cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv cC
    cmul co cA cmul co c1 cA cmul co cA cA cr wcel cB cr wcel cC cr wcel cC cc0
    wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv cC cmul co c1
    cA cmul cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC
    vx cv cmul co c1 wceq wa wa vx cv cC cmul co cC vx cv cmul co c1 cA cr wcel
    cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1
    wceq wa wa vx cv cr wcel cC cr wcel vx cv cC cmul co cC vx cv cmul co wceq
    cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv
    cmul co c1 wceq simprl cC cr wcel cC cc0 wne cA cr wcel cB cr wcel vx cv cr
    wcel cC vx cv cmul co c1 wceq wa simpl3l vx cv cC ax-apostolmul1 syl2anc cA
    cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul
    co c1 wceq simprr eqtrd oveq1d cA cr wcel cB cr wcel cC cr wcel cC cc0 wne
    wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa cA cr wcel c1 cA cmul
    co cA wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa vx cv cr wcel cC
    vx cv cmul co c1 wceq wa simpl1 cA ax-apostolmul4 syl eqtrd eqtrd adantr cA
    cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul
    co c1 wceq wa wa cC cA cmul co cC cB cmul co wceq wa vx cv cC cA cmul co
    cmul co vx cv cC cB cmul co cmul co cA cC cA cmul co cC cB cmul co wceq vx
    cv cC cA cmul co cmul co vx cv cC cB cmul co cmul co wceq cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa
    wa cC cA cmul co cC cB cmul co vx cv cmul oveq2 adantl eqeq1d mpbid cA cr
    wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co
    c1 wceq wa wa vx cv cC cB cmul co cmul co cB wceq cC cA cmul co cC cB cmul
    co wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC
    vx cv cmul co c1 wceq wa wa vx cv cC cB cmul co cmul co vx cv cC cmul co cB
    cmul co cB cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel
    cC vx cv cmul co c1 wceq wa wa vx cv cr wcel cC cr wcel cB cr wcel vx cv cC
    cB cmul co cmul co vx cv cC cmul co cB cmul co wceq cA cr wcel cB cr wcel
    cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq simprl
    cC cr wcel cC cc0 wne cA cr wcel cB cr wcel vx cv cr wcel cC vx cv cmul co
    c1 wceq wa simpl3l cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa vx cv cr
    wcel cC vx cv cmul co c1 wceq wa simpl2 vx cv cC cB ax-apostolmul2 syl3anc
    cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv
    cmul co c1 wceq wa wa vx cv cC cmul co cB cmul co c1 cB cmul co cB cA cr
    wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co
    c1 wceq wa wa vx cv cC cmul co c1 cB cmul cA cr wcel cB cr wcel cC cr wcel
    cC cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv cC
    cmul co cC vx cv cmul co c1 cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa
    w3a vx cv cr wcel cC vx cv cmul co c1 wceq wa wa vx cv cr wcel cC cr wcel
    vx cv cC cmul co cC vx cv cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC
    cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq simprl cC cr wcel cC
    cc0 wne cA cr wcel cB cr wcel vx cv cr wcel cC vx cv cmul co c1 wceq wa
    simpl3l vx cv cC ax-apostolmul1 syl2anc cA cr wcel cB cr wcel cC cr wcel cC
    cc0 wne wa w3a vx cv cr wcel cC vx cv cmul co c1 wceq simprr eqtrd oveq1d
    cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa w3a vx cv cr wcel cC vx cv
    cmul co c1 wceq wa wa cB cr wcel c1 cB cmul co cB wceq cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa vx cv cr wcel cC vx cv cmul co c1 wceq wa
    simpl2 cB ax-apostolmul4 syl eqtrd eqtrd adantr eqtr3d ex rexlimddv cA cB
    wceq cC cA cmul co cC cB cmul co wceq wi cA cr wcel cB cr wcel cC cr wcel
    cC cc0 wne wa w3a cA cB cC cmul oveq2 a1i impbid $.
$}

${
  $d x y $.
  $d x A $. $d x B $.
  $d y A $. $d y B $.

  apostoli.8 $p |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) -> E! x e. RR ( B x. x ) = A ) $=
    cA cr wcel cB cr wcel cB cc0 wne w3a cB vy cv cmul co c1 wceq cB vx cv cmul
    co cA wceq vx cr wreu vy cr cA cr wcel cB cr wcel cB cc0 wne w3a cB cr wcel
    cB cc0 wne wa cB vy cv cmul co c1 wceq vy cr wrex cA cr wcel cB cr wcel cB
    cc0 wne 3simpc vy cB ax-apostol6 syl cA cr wcel cB cr wcel cB cc0 wne w3a
    vy cv cr wcel cB vy cv cmul co c1 wceq wa wa vy cv cA cmul co cr wcel cB vx
    cv cmul co cA wceq vx cv vy cv cA cmul co wceq wb vx cr wral cB vx cv cmul
    co cA wceq vx cr wreu cA cr wcel cB cr wcel cB cc0 wne w3a vy cv cr wcel cB
    vy cv cmul co c1 wceq wa wa vy cv cA cA cr wcel cB cr wcel cB cc0 wne w3a
    vy cv cr wcel cB vy cv cmul co c1 wceq simprl cA cr wcel cB cr wcel cB cc0
    wne vy cv cr wcel cB vy cv cmul co c1 wceq wa simpl1 remulcld cA cr wcel cB
    cr wcel cB cc0 wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq wa wa cB vx
    cv cmul co cA wceq vx cv vy cv cA cmul co wceq wb vx cr cA cr wcel cB cr
    wcel cB cc0 wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr
    wcel wa cB vx cv cmul co cB vy cv cA cmul co cmul co wceq cB vx cv cmul co
    cA wceq vx cv vy cv cA cmul co wceq cA cr wcel cB cr wcel cB cc0 wne w3a vy
    cv cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr wcel wa cB vy cv cA cmul
    co cmul co cA cB vx cv cmul co cA cr wcel cB cr wcel cB cc0 wne w3a vy cv
    cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr wcel wa cB vy cv cA cmul co
    cmul co cB vy cv cmul co cA cmul co c1 cA cmul co cA cA cr wcel cB cr wcel
    cB cc0 wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr wcel
    wa cB cr wcel vy cv cr wcel cA cr wcel cB vy cv cA cmul co cmul co cB vy cv
    cmul co cA cmul co wceq cA cr wcel cB cr wcel cB cc0 wne vy cv cr wcel cB
    vy cv cmul co c1 wceq wa vx cv cr wcel simpll2 cA cr wcel cB cr wcel cB cc0
    wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq vx cv cr wcel simplrl cA cr
    wcel cB cr wcel cB cc0 wne vy cv cr wcel cB vy cv cmul co c1 wceq wa vx cv
    cr wcel simpll1 cB vy cv cA ax-apostolmul2 syl3anc cA cr wcel cB cr wcel cB
    cc0 wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr wcel wa
    cB vy cv cmul co c1 cA cmul cA cr wcel cB cr wcel cB cc0 wne w3a vy cv cr
    wcel cB vy cv cmul co c1 wceq vx cv cr wcel simplrr oveq1d cA cr wcel cB cr
    wcel cB cc0 wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr
    wcel wa cA cr wcel c1 cA cmul co cA wceq cA cr wcel cB cr wcel cB cc0 wne
    vy cv cr wcel cB vy cv cmul co c1 wceq wa vx cv cr wcel simpll1 cA
    ax-apostolmul4 syl 3eqtrd eqeq2d cA cr wcel cB cr wcel cB cc0 wne w3a vy cv
    cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr wcel wa vx cv cr wcel vy cv
    cA cmul co cr wcel cB cr wcel cB cc0 wne wa cB vx cv cmul co cB vy cv cA
    cmul co cmul co wceq vx cv vy cv cA cmul co wceq wb cA cr wcel cB cr wcel
    cB cc0 wne w3a vy cv cr wcel cB vy cv cmul co c1 wceq wa wa vx cv cr wcel
    simpr cA cr wcel cB cr wcel cB cc0 wne w3a vy cv cr wcel cB vy cv cmul co
    c1 wceq wa wa vx cv cr wcel wa vy cv cA cA cr wcel cB cr wcel cB cc0 wne
    w3a vy cv cr wcel cB vy cv cmul co c1 wceq vx cv cr wcel simplrl cA cr wcel
    cB cr wcel cB cc0 wne vy cv cr wcel cB vy cv cmul co c1 wceq wa vx cv cr
    wcel simpll1 remulcld cA cr wcel cB cr wcel cB cc0 wne w3a vy cv cr wcel cB
    vy cv cmul co c1 wceq wa wa vx cv cr wcel wa cB cr wcel cB cc0 wne cA cr
    wcel cB cr wcel cB cc0 wne vy cv cr wcel cB vy cv cmul co c1 wceq wa vx cv
    cr wcel simpll2 cA cr wcel cB cr wcel cB cc0 wne vy cv cr wcel cB vy cv
    cmul co c1 wceq wa vx cv cr wcel simpll3 jca vx cv vy cv cA cmul co cB
    apostoli.7 syl3anc bitr3d ralrimiva cB vx cv cmul co cA wceq vx cr vy cv cA
    cmul co reu6i syl2anc rexlimddv $.
$}

${
  $d x A $. $d x B $.

  redivval $p |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) -> ( A / B ) = ( iota_ x e. RR ( B x. x ) = A ) ) $=
    cA cr wcel cB cr wcel cB cc0 wne w3a cA cB cdiv co cB vx cv cmul co cA wceq
    vx cc crio cB vx cv cmul co cA wceq vx cr crio cA cr wcel cA cc wcel cB cr
    wcel cB cc wcel cB cc0 wne cB cc0 wne cA cB cdiv co cB vx cv cmul co cA
    wceq vx cc crio wceq cr cc cA ax-resscn sseli cr cc cB ax-resscn sseli cB
    cc0 wne id vx cA cB divval syl3an cA cr wcel cB cr wcel cB cc0 wne w3a cB
    vx cv cmul co cA wceq vx cr wrex cB vx cv cmul co cA wceq vx cc wreu cB vx
    cv cmul co cA wceq vx cr crio cB vx cv cmul co cA wceq vx cc crio wceq cA
    cr wcel cB cr wcel cB cc0 wne w3a cB vx cv cmul co cA wceq vx cr wreu cB vx
    cv cmul co cA wceq vx cr wrex vx cA cB apostoli.8 cB vx cv cmul co cA wceq
    vx cr reurex syl cA cr wcel cA cc wcel cB cr wcel cB cc wcel cB cc0 wne cB
    cc0 wne cB vx cv cmul co cA wceq vx cc wreu cr cc cA ax-resscn sseli cr cc
    cB ax-resscn sseli cB cc0 wne id vx cA cB receu syl3an cr cc wss cB vx cv
    cmul co cA wceq vx cr wrex cB vx cv cmul co cA wceq vx cc wreu cB vx cv
    cmul co cA wceq vx cr crio cB vx cv cmul co cA wceq vx cc crio wceq
    ax-resscn cB vx cv cmul co cA wceq vx cr cc riotass mp3an1 syl2anc eqtr4d
    $.
$}

${
  $d x A $.

  rerecid $p |- ( ( A e. RR /\ A =/= 0 ) -> ( A x. ( 1 / A ) ) = 1 ) $=
    cA cr wcel cA cc0 wne wa cA c1 cA cdiv co cmul co c1 wceq cA vx cv cmul co
    c1 wceq vx cr crio c1 cA cdiv co wceq cA cr wcel cA cc0 wne wa c1 cA cdiv
    co cA vx cv cmul co c1 wceq vx cr crio c1 cr wcel cA cr wcel cA cc0 wne c1
    cA cdiv co cA vx cv cmul co c1 wceq vx cr crio wceq 1re vx c1 cA redivval
    mp3an1 eqcomd cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA vx cv cmul
    co c1 wceq vx cr wreu cA c1 cA cdiv co cmul co c1 wceq cA vx cv cmul co c1
    wceq vx cr crio c1 cA cdiv co wceq wb c1 cr wcel cA cr wcel cA cc0 wne c1
    cA cdiv co cr wcel 1re c1 cA redivcl mp3an1 c1 cr wcel cA cr wcel cA cc0
    wne cA vx cv cmul co c1 wceq vx cr wreu 1re vx c1 cA apostoli.8 mp3an1 cA
    vx cv cmul co c1 wceq cA c1 cA cdiv co cmul co c1 wceq vx cr c1 cA cdiv co
    vx cv c1 cA cdiv co wceq cA vx cv cmul co cA c1 cA cdiv co cmul co c1 vx cv
    c1 cA cdiv co cA cmul oveq2 eqeq1d riota2 syl2anc mpbird $.
$}

${
  $d x A $. $d x B $.

  apostoli.9 $p |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) -> ( A / B ) = ( A x. ( 1 / B ) ) ) $=
    cA cr wcel cB cr wcel cB cc0 wne w3a cB cA cB cdiv co cmul co cB cA c1 cB
    cdiv co cmul co cmul co wceq cA cB cdiv co cA c1 cB cdiv co cmul co wceq cA
    cr wcel cB cr wcel cB cc0 wne w3a cB cA cB cdiv co cmul co cB c1 cB cdiv co
    cmul co cA cmul co cB c1 cB cdiv co cA cmul co cmul co cB cA c1 cB cdiv co
    cmul co cmul co cA cr wcel cB cr wcel cB cc0 wne w3a cB cA cB cdiv co cmul
    co cA cB c1 cB cdiv co cmul co cA cmul co cA cr wcel cB cr wcel cB cc0 wne
    w3a cB cA cB cdiv co cmul co cA wceq cB vx cv cmul co cA wceq vx cr crio cA
    cB cdiv co wceq cA cr wcel cB cr wcel cB cc0 wne w3a cA cB cdiv co cB vx cv
    cmul co cA wceq vx cr crio vx cA cB redivval eqcomd cA cr wcel cB cr wcel
    cB cc0 wne w3a cA cB cdiv co cr wcel cB vx cv cmul co cA wceq vx cr wreu cB
    cA cB cdiv co cmul co cA wceq cB vx cv cmul co cA wceq vx cr crio cA cB
    cdiv co wceq wb cA cB redivcl vx cA cB apostoli.8 cB vx cv cmul co cA wceq
    cB cA cB cdiv co cmul co cA wceq vx cr cA cB cdiv co vx cv cA cB cdiv co
    wceq cB vx cv cmul co cB cA cB cdiv co cmul co cA vx cv cA cB cdiv co cB
    cmul oveq2 eqeq1d riota2 syl2anc mpbird cA cr wcel cB cr wcel cB cc0 wne
    w3a cB c1 cB cdiv co cmul co cA cmul co c1 cA cmul co cA cA cr wcel cB cr
    wcel cB cc0 wne w3a cB c1 cB cdiv co cmul co c1 cA cmul cB cr wcel cB cc0
    wne cB c1 cB cdiv co cmul co c1 wceq cA cr wcel cB rerecid 3adant1 oveq1d
    cA cr wcel cB cr wcel c1 cA cmul co cA wceq cB cc0 wne cA ax-apostolmul4
    3ad2ant1 eqtrd eqtr4d cA cr wcel cB cr wcel cB cc0 wne w3a cB cr wcel c1 cB
    cdiv co cr wcel cA cr wcel cB c1 cB cdiv co cA cmul co cmul co cB c1 cB
    cdiv co cmul co cA cmul co wceq cA cr wcel cB cr wcel cB cc0 wne simp2 cA
    cr wcel cB cr wcel cB cc0 wne w3a cB cA cr wcel cB cr wcel cB cc0 wne simp2
    cA cr wcel cB cr wcel cB cc0 wne simp3 rereccld cA cr wcel cB cr wcel cB
    cc0 wne simp1 cB c1 cB cdiv co cA ax-apostolmul2 syl3anc cA cr wcel cB cr
    wcel cB cc0 wne w3a c1 cB cdiv co cA cmul co cA c1 cB cdiv co cmul co cB
    cmul cA cr wcel cB cr wcel cB cc0 wne w3a c1 cB cdiv co cr wcel cA cr wcel
    c1 cB cdiv co cA cmul co cA c1 cB cdiv co cmul co wceq cA cr wcel cB cr
    wcel cB cc0 wne w3a cB cA cr wcel cB cr wcel cB cc0 wne simp2 cA cr wcel cB
    cr wcel cB cc0 wne simp3 rereccld cA cr wcel cB cr wcel cB cc0 wne simp1 c1
    cB cdiv co cA ax-apostolmul1 syl2anc oveq2d 3eqtr2d cA cr wcel cB cr wcel
    cB cc0 wne w3a cA cB cdiv co cr wcel cA c1 cB cdiv co cmul co cr wcel cB cr
    wcel cB cc0 wne wa cB cA cB cdiv co cmul co cB cA c1 cB cdiv co cmul co
    cmul co wceq cA cB cdiv co cA c1 cB cdiv co cmul co wceq wb cA cB redivcl
    cA cr wcel cB cr wcel cB cc0 wne w3a cA c1 cB cdiv co cA cr wcel cB cr wcel
    cB cc0 wne simp1 cA cr wcel cB cr wcel cB cc0 wne w3a cB cA cr wcel cB cr
    wcel cB cc0 wne simp2 cA cr wcel cB cr wcel cB cc0 wne simp3 rereccld
    remulcld cA cr wcel cB cr wcel cB cc0 wne 3simpc cA cB cdiv co cA c1 cB
    cdiv co cmul co cB apostoli.7 syl3anc mpbid $.
$}

${
  rerecne0 $p |- ( ( A e. RR /\ A =/= 0 ) -> ( 1 / A ) =/= 0 ) $=
    cA cr wcel cA cc0 wne wa c1 cA cdiv co cc0 cA cr wcel cA cc0 wne wa c1 cA
    cdiv co cc0 wceq c1 cc0 wceq cA cr wcel cA cc0 wne wa c1 cA cdiv co cc0
    wceq wa cA c1 cA cdiv co cmul co c1 cc0 cA cr wcel cA cc0 wne wa cA c1 cA
    cdiv co cmul co c1 wceq c1 cA cdiv co cc0 wceq cA rerecid adantr cA cr wcel
    cA cc0 wne wa c1 cA cdiv co cc0 wceq wa cA c1 cA cdiv co cmul co cA cc0
    cmul co cc0 cA cr wcel cA cc0 wne wa c1 cA cdiv co cc0 wceq wa c1 cA cdiv
    co cc0 cA cmul cA cr wcel cA cc0 wne wa c1 cA cdiv co cc0 wceq simpr oveq2d
    cA cr wcel cA cc0 wne wa c1 cA cdiv co cc0 wceq wa cA cr wcel cA cc0 cmul
    co cc0 wceq cA cr wcel cA cc0 wne c1 cA cdiv co cc0 wceq simpll cA
    apostoli.6 syl eqtrd eqtr3d c1 cc0 wceq wn cA cr wcel cA cc0 wne wa c1 cA
    cdiv co cc0 wceq wa c1 cc0 ax-1ne0 neii a1i pm2.65da neqned $.
$}

${
  apostoli.10 $p |- ( ( A e. RR /\ A =/= 0 ) -> ( 1 / ( 1 / A ) ) = A ) $=
    cA cr wcel cA cc0 wne wa c1 cA cdiv co c1 c1 cA cdiv co cdiv co cmul co c1
    cA cdiv co cA cmul co wceq c1 c1 cA cdiv co cdiv co cA wceq cA cr wcel cA
    cc0 wne wa cA c1 cA cdiv co cmul co c1 c1 cA cdiv co cA cmul co c1 cA cdiv
    co c1 c1 cA cdiv co cdiv co cmul co cA rerecid cA cr wcel cA cc0 wne wa c1
    cA cdiv co cr wcel cA cr wcel c1 cA cdiv co cA cmul co cA c1 cA cdiv co
    cmul co wceq cA rereccl cA cr wcel cA cc0 wne simpl c1 cA cdiv co cA
    ax-apostolmul1 syl2anc cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel c1 cA
    cdiv co cc0 wne c1 cA cdiv co c1 c1 cA cdiv co cdiv co cmul co c1 wceq cA
    rereccl cA rerecne0 c1 cA cdiv co rerecid syl2anc 3eqtr4rd cA cr wcel cA
    cc0 wne wa c1 c1 cA cdiv co cdiv co cr wcel cA cr wcel c1 cA cdiv co cr
    wcel c1 cA cdiv co cc0 wne wa c1 cA cdiv co c1 c1 cA cdiv co cdiv co cmul
    co c1 cA cdiv co cA cmul co wceq c1 c1 cA cdiv co cdiv co cA wceq wb cA cr
    wcel cA cc0 wne wa c1 cA cdiv co cA rereccl cA rerecne0 rereccld cA cr wcel
    cA cc0 wne simpl cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel c1 cA cdiv
    co cc0 wne cA rereccl cA rerecne0 jca c1 c1 cA cdiv co cdiv co cA c1 cA
    cdiv co apostoli.7 syl3anc mpbid $.
$}

${
  apostoli.11 $p |- ( ( A e. RR /\ B e. RR ) -> ( ( A x. B ) = 0 <-> ( A = 0 \/ B = 0 ) ) ) $=
    cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wceq cB cc0 wceq wo
    cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wceq cB cc0 wceq wo
    cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq wa cA cc0 wceq cB cc0 wceq
    cA cc0 wceq wn cA cc0 wne cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq
    wa cB cc0 wceq cA cc0 df-ne cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq
    cA cc0 wne cB cc0 wceq cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA
    cc0 wne w3a cB c1 cA cdiv co cc0 cmul co cc0 cA cr wcel cB cr wcel wa cA cB
    cmul co cc0 wceq cA cc0 wne w3a c1 cA cdiv co cA cB cmul co cmul co cB c1
    cA cdiv co cc0 cmul co cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA
    cc0 wne w3a c1 cA cdiv co cA cB cmul co cmul co c1 cA cdiv co cA cmul co cB
    cmul co cB cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wne w3a
    c1 cA cdiv co cr wcel cA cr wcel cB cr wcel c1 cA cdiv co cA cB cmul co
    cmul co c1 cA cdiv co cA cmul co cB cmul co wceq cA cr wcel cB cr wcel wa
    cA cB cmul co cc0 wceq cA cc0 wne w3a cA cr wcel cA cc0 wne c1 cA cdiv co
    cr wcel cA cr wcel cB cr wcel cA cB cmul co cc0 wceq cA cc0 wne simp1l cA
    cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wne simp3 cA rereccl
    syl2anc cA cr wcel cB cr wcel cA cB cmul co cc0 wceq cA cc0 wne simp1l cA
    cr wcel cB cr wcel cA cB cmul co cc0 wceq cA cc0 wne simp1r c1 cA cdiv co
    cA cB ax-apostolmul2 syl3anc cA cr wcel cB cr wcel wa cA cB cmul co cc0
    wceq cA cc0 wne w3a c1 cA cdiv co cA cmul co cB cmul co c1 cB cmul co cB cA
    cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wne w3a cA cr wcel cA
    cc0 wne c1 cA cdiv co cA cmul co cB cmul co c1 cB cmul co wceq cA cr wcel
    cB cr wcel cA cB cmul co cc0 wceq cA cc0 wne simp1l cA cr wcel cB cr wcel
    wa cA cB cmul co cc0 wceq cA cc0 wne simp3 cA cr wcel cA cc0 wne wa cA c1
    cA cdiv co cmul co cB cmul co c1 cA cdiv co cA cmul co cB cmul co c1 cB
    cmul co cA cr wcel cA cc0 wne wa cA c1 cA cdiv co cmul co c1 cA cdiv co cA
    cmul co cB cmul cA cr wcel cA cc0 wne wa cA cr wcel c1 cA cdiv co cr wcel
    cA c1 cA cdiv co cmul co c1 cA cdiv co cA cmul co wceq cA cr wcel cA cc0
    wne simpl cA rereccl cA c1 cA cdiv co ax-apostolmul1 syl2anc oveq1d cA cr
    wcel cA cc0 wne wa cA c1 cA cdiv co cmul co c1 cB cmul cA rerecid oveq1d
    eqtr3d syl2anc cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wne
    w3a cB cr wcel c1 cB cmul co cB wceq cA cr wcel cB cr wcel cA cB cmul co
    cc0 wceq cA cc0 wne simp1r cB ax-apostolmul4 syl eqtrd eqtrd cA cB cmul co
    cc0 wceq cA cr wcel cB cr wcel wa c1 cA cdiv co cA cB cmul co cmul co c1 cA
    cdiv co cc0 cmul co wceq cA cc0 wne cA cB cmul co cc0 c1 cA cdiv co cmul
    oveq2 3ad2ant2 eqtr3d cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA
    cc0 wne w3a c1 cA cdiv co cr wcel c1 cA cdiv co cc0 cmul co cc0 wceq cA cr
    wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wne w3a cA cr wcel cA cc0
    wne c1 cA cdiv co cr wcel cA cr wcel cB cr wcel cA cB cmul co cc0 wceq cA
    cc0 wne simp1l cA cr wcel cB cr wcel wa cA cB cmul co cc0 wceq cA cc0 wne
    simp3 cA rereccl syl2anc c1 cA cdiv co apostoli.6 syl eqtrd 3expia syl5bir
    orrd ex cA cr wcel cB cr wcel wa cA cc0 wceq cA cB cmul co cc0 wceq cB cc0
    wceq cB cr wcel cA cc0 wceq cA cB cmul co cc0 wceq wi cA cr wcel cB cr wcel
    cA cc0 wceq cA cB cmul co cc0 wceq cB cr wcel cA cc0 wceq wa cA cB cmul co
    cc0 cB cmul co cc0 cA cc0 wceq cA cB cmul co cc0 cB cmul co wceq cB cr wcel
    cA cc0 cB cmul oveq1 adantl cB cr wcel cc0 cB cmul co cc0 wceq cA cc0 wceq
    cB cr wcel cc0 cB cmul co cB cc0 cmul co cc0 cc0 cr wcel cB cr wcel cc0 cB
    cmul co cB cc0 cmul co wceq 0re cc0 cB ax-apostolmul1 mpan cB apostoli.6
    eqtrd adantr eqtrd ex adantl cA cr wcel cB cc0 wceq cA cB cmul co cc0 wceq
    wi cB cr wcel cA cr wcel cB cc0 wceq cA cB cmul co cc0 wceq cA cr wcel cB
    cc0 wceq wa cA cB cmul co cA cc0 cmul co cc0 cB cc0 wceq cA cB cmul co cA
    cc0 cmul co wceq cA cr wcel cB cc0 cA cmul oveq2 adantl cA cr wcel cA cc0
    cmul co cc0 wceq cB cc0 wceq cA apostoli.6 adantr eqtrd ex adantr jaod
    impbid $.
$}

${
  apostoli.12 $p |- ( ( A e. RR /\ B e. RR ) -> ( ( -u A x. B ) = -u ( A x. B ) /\ ( -u A x. -u B ) = ( A x. B ) ) ) $=
    cA cr wcel cB cr wcel wa cA cneg cB cmul co cA cB cmul co cneg wceq cA cneg
    cB cneg cmul co cA cB cmul co wceq cA cr wcel cB cr wcel wa cA cneg cB cmul
    co cA cB cmul co cneg wceq cB cA cA cneg caddc co cmul co cc0 wceq cA cr
    wcel cB cr wcel wa cB cA cA cneg caddc co cmul co cB cc0 cmul co cc0 cA cr
    wcel cB cA cA cneg caddc co cmul co cB cc0 cmul co wceq cB cr wcel cA cr
    wcel cA cA cneg caddc co cc0 cB cmul cA renegid oveq2d adantr cB cr wcel cB
    cc0 cmul co cc0 wceq cA cr wcel cB apostoli.6 adantl eqtrd cA cr wcel cB cr
    wcel wa cA cB cmul co cA cneg cB cmul co caddc co cA cB cmul co cA cB cmul
    co cneg caddc co wceq cA cB cmul co cA cneg cB cmul co caddc co cc0 wceq cA
    cneg cB cmul co cA cB cmul co cneg wceq cB cA cA cneg caddc co cmul co cc0
    wceq cA cr wcel cB cr wcel wa cA cB cmul co cA cB cmul co cneg caddc co cc0
    cA cB cmul co cA cneg cB cmul co caddc co cA cr wcel cB cr wcel wa cA cB
    cmul co cr wcel cA cB cmul co cA cB cmul co cneg caddc co cc0 wceq cA cr
    wcel cB cr wcel wa cA cB cA cr wcel cB cr wcel simpl cA cr wcel cB cr wcel
    simpr remulcld cA cB cmul co renegid syl eqeq2d cA cr wcel cB cr wcel wa cA
    cB cmul co cr wcel cA cneg cB cmul co cr wcel cA cB cmul co cneg cr wcel cA
    cB cmul co cA cneg cB cmul co caddc co cA cB cmul co cA cB cmul co cneg
    caddc co wceq cA cneg cB cmul co cA cB cmul co cneg wceq wb cA cr wcel cB
    cr wcel wa cA cB cA cr wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr
    remulcld cA cr wcel cB cr wcel wa cA cneg cB cA cr wcel cB cr wcel wa cA cA
    cr wcel cB cr wcel simpl renegcld cA cr wcel cB cr wcel simpr remulcld cA
    cr wcel cB cr wcel wa cA cB cmul co cA cr wcel cB cr wcel wa cA cB cA cr
    wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr remulcld renegcld cA cB
    cmul co cA cneg cB cmul co cA cB cmul co cneg apostoli.1 syl3anc cA cr wcel
    cB cr wcel wa cA cB cmul co cA cneg cB cmul co caddc co cB cA cA cneg caddc
    co cmul co cc0 cA cr wcel cB cr wcel wa cA cB cmul co cB cA cneg cmul co
    caddc co cB cA cmul co cB cA cneg cmul co caddc co cA cB cmul co cA cneg cB
    cmul co caddc co cB cA cA cneg caddc co cmul co cA cr wcel cB cr wcel wa cA
    cB cmul co cB cA cmul co cB cA cneg cmul co caddc cA cB ax-apostolmul1
    oveq1d cA cr wcel cB cr wcel wa cA cneg cr wcel cB cr wcel cA cB cmul co cA
    cneg cB cmul co caddc co cA cB cmul co cB cA cneg cmul co caddc co wceq cA
    cr wcel cB cr wcel wa cA cA cr wcel cB cr wcel simpl renegcld cA cr wcel cB
    cr wcel simpr cA cneg cr wcel cB cr wcel wa cA cneg cB cmul co cB cA cneg
    cmul co cA cB cmul co caddc cA cneg cB ax-apostolmul1 oveq2d syl2anc cA cr
    wcel cB cr wcel wa cB cr wcel cA cr wcel cA cneg cr wcel cB cA cA cneg
    caddc co cmul co cB cA cmul co cB cA cneg cmul co caddc co wceq cA cr wcel
    cB cr wcel simpr cA cr wcel cB cr wcel simpl cA cr wcel cB cr wcel wa cA cA
    cr wcel cB cr wcel simpl renegcld cB cA cA cneg ax-apostol3 syl3anc 3eqtr4d
    eqeq1d 3bitr3d mpbird cA cr wcel cB cr wcel wa cA cB cmul co cneg cA cneg
    cB cneg cmul co caddc co cA cB cmul co cneg cA cB cmul co caddc co wceq cA
    cneg cB cneg cmul co cA cB cmul co wceq cA cr wcel cB cr wcel wa cA cneg cB
    cneg cmul co cA cB cmul co cneg caddc co cA cB cmul co cA cB cmul co cneg
    caddc co cA cB cmul co cneg cA cneg cB cneg cmul co caddc co cA cB cmul co
    cneg cA cB cmul co caddc co cA cr wcel cB cr wcel wa cA cneg cB cneg cmul
    co cA cB cmul co cneg caddc co cc0 cA cB cmul co cA cB cmul co cneg caddc
    co cA cr wcel cB cr wcel wa cA cneg cB cneg cmul co cA cneg cB cmul co
    caddc co cA cneg cB cneg cmul co cA cB cmul co cneg caddc co cc0 cA cr wcel
    cB cr wcel wa cA cneg cB cmul co cA cB cmul co cneg cA cneg cB cneg cmul co
    caddc cA cr wcel cB cr wcel wa cA cneg cB cmul co cA cB cmul co cneg wceq
    cB cA cA cneg caddc co cmul co cc0 wceq cA cr wcel cB cr wcel wa cB cA cA
    cneg caddc co cmul co cB cc0 cmul co cc0 cA cr wcel cB cA cA cneg caddc co
    cmul co cB cc0 cmul co wceq cB cr wcel cA cr wcel cA cA cneg caddc co cc0
    cB cmul cA renegid oveq2d adantr cB cr wcel cB cc0 cmul co cc0 wceq cA cr
    wcel cB apostoli.6 adantl eqtrd cA cr wcel cB cr wcel wa cA cB cmul co cA
    cneg cB cmul co caddc co cA cB cmul co cA cB cmul co cneg caddc co wceq cA
    cB cmul co cA cneg cB cmul co caddc co cc0 wceq cA cneg cB cmul co cA cB
    cmul co cneg wceq cB cA cA cneg caddc co cmul co cc0 wceq cA cr wcel cB cr
    wcel wa cA cB cmul co cA cB cmul co cneg caddc co cc0 cA cB cmul co cA cneg
    cB cmul co caddc co cA cr wcel cB cr wcel wa cA cB cmul co cr wcel cA cB
    cmul co cA cB cmul co cneg caddc co cc0 wceq cA cr wcel cB cr wcel wa cA cB
    cA cr wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr remulcld cA cB cmul
    co renegid syl eqeq2d cA cr wcel cB cr wcel wa cA cB cmul co cr wcel cA
    cneg cB cmul co cr wcel cA cB cmul co cneg cr wcel cA cB cmul co cA cneg cB
    cmul co caddc co cA cB cmul co cA cB cmul co cneg caddc co wceq cA cneg cB
    cmul co cA cB cmul co cneg wceq wb cA cr wcel cB cr wcel wa cA cB cA cr
    wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr remulcld cA cr wcel cB cr
    wcel wa cA cneg cB cA cr wcel cB cr wcel wa cA cA cr wcel cB cr wcel simpl
    renegcld cA cr wcel cB cr wcel simpr remulcld cA cr wcel cB cr wcel wa cA
    cB cmul co cA cr wcel cB cr wcel wa cA cB cA cr wcel cB cr wcel simpl cA cr
    wcel cB cr wcel simpr remulcld renegcld cA cB cmul co cA cneg cB cmul co cA
    cB cmul co cneg apostoli.1 syl3anc cA cr wcel cB cr wcel wa cA cB cmul co
    cA cneg cB cmul co caddc co cB cA cA cneg caddc co cmul co cc0 cA cr wcel
    cB cr wcel wa cA cB cmul co cB cA cneg cmul co caddc co cB cA cmul co cB cA
    cneg cmul co caddc co cA cB cmul co cA cneg cB cmul co caddc co cB cA cA
    cneg caddc co cmul co cA cr wcel cB cr wcel wa cA cB cmul co cB cA cmul co
    cB cA cneg cmul co caddc cA cB ax-apostolmul1 oveq1d cA cr wcel cB cr wcel
    wa cA cneg cr wcel cB cr wcel cA cB cmul co cA cneg cB cmul co caddc co cA
    cB cmul co cB cA cneg cmul co caddc co wceq cA cr wcel cB cr wcel wa cA cA
    cr wcel cB cr wcel simpl renegcld cA cr wcel cB cr wcel simpr cA cneg cr
    wcel cB cr wcel wa cA cneg cB cmul co cB cA cneg cmul co cA cB cmul co
    caddc cA cneg cB ax-apostolmul1 oveq2d syl2anc cA cr wcel cB cr wcel wa cB
    cr wcel cA cr wcel cA cneg cr wcel cB cA cA cneg caddc co cmul co cB cA
    cmul co cB cA cneg cmul co caddc co wceq cA cr wcel cB cr wcel simpr cA cr
    wcel cB cr wcel simpl cA cr wcel cB cr wcel wa cA cA cr wcel cB cr wcel
    simpl renegcld cB cA cA cneg ax-apostol3 syl3anc 3eqtr4d eqeq1d 3bitr3d
    mpbird oveq2d cA cr wcel cB cr wcel wa cA cneg cB cneg cB caddc co cmul co
    cA cneg cc0 cmul co cA cneg cB cneg cmul co cA cneg cB cmul co caddc co cc0
    cA cr wcel cB cr wcel wa cB cneg cB caddc co cc0 cA cneg cmul cA cr wcel cB
    cr wcel wa cB cneg cB caddc co cB cB cneg caddc co cc0 cA cr wcel cB cr
    wcel wa cB cneg cr wcel cB cr wcel cB cneg cB caddc co cB cB cneg caddc co
    wceq cA cr wcel cB cr wcel wa cB cA cr wcel cB cr wcel simpr renegcld cA cr
    wcel cB cr wcel simpr cB cneg cB ax-apostoladd1 syl2anc cA cr wcel cB cr
    wcel wa cB cr wcel cB cB cneg caddc co cc0 wceq cA cr wcel cB cr wcel simpr
    cB renegid syl eqtrd oveq2d cA cr wcel cB cr wcel wa cA cneg cr wcel cB
    cneg cr wcel cB cr wcel cA cneg cB cneg cB caddc co cmul co cA cneg cB cneg
    cmul co cA cneg cB cmul co caddc co wceq cA cr wcel cB cr wcel wa cA cA cr
    wcel cB cr wcel simpl renegcld cA cr wcel cB cr wcel wa cB cA cr wcel cB cr
    wcel simpr renegcld cA cr wcel cB cr wcel simpr cA cneg cB cneg cB
    ax-apostol3 syl3anc cA cr wcel cB cr wcel wa cA cneg cr wcel cA cneg cc0
    cmul co cc0 wceq cA cr wcel cB cr wcel wa cA cA cr wcel cB cr wcel simpl
    renegcld cA cneg apostoli.6 syl 3eqtr3d eqtr3d cA cr wcel cB cr wcel wa cA
    cB cmul co cr wcel cA cB cmul co cA cB cmul co cneg caddc co cc0 wceq cA cr
    wcel cB cr wcel wa cA cB cA cr wcel cB cr wcel simpl cA cr wcel cB cr wcel
    simpr remulcld cA cB cmul co renegid syl eqtr4d cA cr wcel cB cr wcel wa cA
    cB cmul co cneg cr wcel cA cneg cB cneg cmul co cr wcel cA cB cmul co cneg
    cA cneg cB cneg cmul co caddc co cA cneg cB cneg cmul co cA cB cmul co cneg
    caddc co wceq cA cr wcel cB cr wcel wa cA cB cmul co cA cr wcel cB cr wcel
    wa cA cB cA cr wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr remulcld
    renegcld cA cr wcel cB cr wcel wa cA cneg cB cneg cA cr wcel cB cr wcel wa
    cA cA cr wcel cB cr wcel simpl renegcld cA cr wcel cB cr wcel wa cB cA cr
    wcel cB cr wcel simpr renegcld remulcld cA cB cmul co cneg cA cneg cB cneg
    cmul co ax-apostoladd1 syl2anc cA cr wcel cB cr wcel wa cA cB cmul co cneg
    cr wcel cA cB cmul co cr wcel cA cB cmul co cneg cA cB cmul co caddc co cA
    cB cmul co cA cB cmul co cneg caddc co wceq cA cr wcel cB cr wcel wa cA cB
    cmul co cA cr wcel cB cr wcel wa cA cB cA cr wcel cB cr wcel simpl cA cr
    wcel cB cr wcel simpr remulcld renegcld cA cr wcel cB cr wcel wa cA cB cA
    cr wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr remulcld cA cB cmul co
    cneg cA cB cmul co ax-apostoladd1 syl2anc 3eqtr4d cA cr wcel cB cr wcel wa
    cA cB cmul co cneg cr wcel cA cneg cB cneg cmul co cr wcel cA cB cmul co cr
    wcel cA cB cmul co cneg cA cneg cB cneg cmul co caddc co cA cB cmul co cneg
    cA cB cmul co caddc co wceq cA cneg cB cneg cmul co cA cB cmul co wceq wb
    cA cr wcel cB cr wcel wa cA cB cmul co cA cr wcel cB cr wcel wa cA cB cA cr
    wcel cB cr wcel simpl cA cr wcel cB cr wcel simpr remulcld renegcld cA cr
    wcel cB cr wcel wa cA cneg cB cneg cA cr wcel cB cr wcel wa cA cA cr wcel
    cB cr wcel simpl renegcld cA cr wcel cB cr wcel wa cB cA cr wcel cB cr wcel
    simpr renegcld remulcld cA cr wcel cB cr wcel wa cA cB cA cr wcel cB cr
    wcel simpl cA cr wcel cB cr wcel simpr remulcld cA cB cmul co cneg cA cneg
    cB cneg cmul co cA cB cmul co apostoli.1 syl3anc mpbid jca $.
$}

${
  $d x A $. $d x B $.

  rerecdiv2 $p |- ( ( ( A e. RR /\ A =/= 0 ) /\ ( B e. RR /\ B =/= 0 ) ) -> ( ( 1 / A ) / B ) = ( 1 / ( A x. B ) ) ) $=
    cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cB cmul co cdiv
    co c1 cA cdiv co cB cdiv co cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    wa wa cA cB cmul co vx cv cmul co c1 wceq vx cr crio c1 cA cB cmul co cdiv
    co c1 cA cdiv co cB cdiv co cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    wa wa c1 cA cB cmul co cdiv co cA cB cmul co vx cv cmul co c1 wceq vx cr
    crio cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB cmul co cr
    wcel cA cB cmul co cc0 wne c1 cA cB cmul co cdiv co cA cB cmul co vx cv
    cmul co c1 wceq vx cr crio wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0
    wne wa wa cA cB cA cr wcel cA cc0 wne cB cr wcel cB cc0 wne wa simpll cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprl remulcld cA cr wcel cA cc0
    wne wa cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv co
    cmul co cc0 wceq wn cA cB cmul co cc0 wne cA cr wcel cA cc0 wne wa cB cr
    wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv co cmul co cc0 cA
    cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv
    co cB cdiv co cmul co c1 cc0 cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    wa wa cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA cB cmul co c1 cA
    cdiv co cB cdiv co cmul co c1 cA cr wcel cA cc0 wne wa cB cr wcel cB cc0
    wne wa wa cA cr wcel cB cr wcel c1 cA cdiv co cB cdiv co cr wcel cA cB c1
    cA cdiv co cB cdiv co cmul co cmul co cA cB cmul co c1 cA cdiv co cB cdiv
    co cmul co wceq cA cr wcel cA cc0 wne cB cr wcel cB cc0 wne wa simpll cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB
    cr wcel cB cc0 wne wa wa c1 cA cdiv co cB cA cr wcel cA cc0 wne wa cB cr
    wcel cB cc0 wne wa wa cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel
    cA cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr
    wcel cB cc0 wne simprr redivcld cA cB c1 cA cdiv co cB cdiv co
    ax-apostolmul2 syl3anc cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa
    cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA c1 cA cdiv co cmul co c1
    cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cr wcel
    cB cr wcel cB cc0 wne cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA c1
    cA cdiv co cmul co wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr wcel cA cc0 wne wa
    cB cr wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel cA cc0 wne wa cB
    cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    simprr c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a cB c1 cA cdiv co cB
    cdiv co cmul co c1 cA cdiv co cA cmul c1 cA cdiv co cr wcel cB cr wcel cB
    cc0 wne w3a cB c1 cA cdiv co cB cdiv co cmul co c1 c1 cA cdiv co cmul co c1
    cA cdiv co c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a cB c1 cA cdiv co
    cB cdiv co cmul co cB c1 cB cdiv co c1 cA cdiv co cmul co cmul co cB c1 cB
    cdiv co cmul co c1 cA cdiv co cmul co c1 c1 cA cdiv co cmul co c1 cA cdiv
    co cr wcel cB cr wcel cB cc0 wne w3a c1 cA cdiv co cB cdiv co c1 cB cdiv co
    c1 cA cdiv co cmul co cB cmul c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne
    w3a c1 cA cdiv co cB cdiv co c1 cA cdiv co c1 cB cdiv co cmul co c1 cB cdiv
    co c1 cA cdiv co cmul co c1 cA cdiv co cB apostoli.9 c1 cA cdiv co cr wcel
    cB cr wcel cB cc0 wne w3a c1 cA cdiv co cr wcel c1 cB cdiv co cr wcel c1 cA
    cdiv co c1 cB cdiv co cmul co c1 cB cdiv co c1 cA cdiv co cmul co wceq c1
    cA cdiv co cr wcel cB cr wcel cB cc0 wne simp1 cB cr wcel cB cc0 wne c1 cB
    cdiv co cr wcel c1 cA cdiv co cr wcel cB rereccl 3adant1 c1 cA cdiv co c1
    cB cdiv co ax-apostolmul1 syl2anc eqtrd oveq2d c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a cB cr wcel c1 cB cdiv co cr wcel c1 cA cdiv co cr wcel
    cB c1 cB cdiv co c1 cA cdiv co cmul co cmul co cB c1 cB cdiv co cmul co c1
    cA cdiv co cmul co wceq c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne simp2
    cB cr wcel cB cc0 wne c1 cB cdiv co cr wcel c1 cA cdiv co cr wcel cB
    rereccl 3adant1 c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne simp1 cB c1 cB
    cdiv co c1 cA cdiv co ax-apostolmul2 syl3anc c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a cB c1 cB cdiv co cmul co c1 c1 cA cdiv co cmul cB cr
    wcel cB cc0 wne cB c1 cB cdiv co cmul co c1 wceq c1 cA cdiv co cr wcel cB
    rerecid 3adant1 oveq1d 3eqtrd c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne
    w3a c1 cA cdiv co cr wcel c1 c1 cA cdiv co cmul co c1 cA cdiv co wceq c1 cA
    cdiv co cr wcel cB cr wcel cB cc0 wne simp1 c1 cA cdiv co ax-apostolmul4
    syl eqtrd oveq2d syl3anc cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa cA cr wcel cA cc0 wne wa cA c1 cA cdiv co cmul co c1 wceq cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rerecid syl eqtrd eqtr3d c1
    cc0 wne cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa ax-1ne0 a1i
    eqnetrd neneqd cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB
    cmul co c1 cA cdiv co cB cdiv co cmul co cc0 wceq cA cB cmul co cc0 cA cB
    cmul co cc0 wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB
    cmul co c1 cA cdiv co cB cdiv co cmul co cc0 wceq cA cr wcel cA cc0 wne wa
    cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv co cmul co
    cc0 wceq cA cB cmul co cc0 wceq cc0 c1 cA cdiv co cB cdiv co cmul co cc0
    wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cc0 c1 cA cdiv co
    cB cdiv co cmul co c1 cA cdiv co cB cdiv co cc0 cmul co cc0 cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cB cdiv co cr wcel cc0
    c1 cA cdiv co cB cdiv co cmul co c1 cA cdiv co cB cdiv co cc0 cmul co wceq
    cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cB cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cr wcel cA cc0 wne wa c1
    cA cdiv co cr wcel cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa simpl
    cA rereccl syl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprr redivcld cc0 cr wcel c1 cA
    cdiv co cB cdiv co cr wcel cc0 c1 cA cdiv co cB cdiv co cmul co c1 cA cdiv
    co cB cdiv co cc0 cmul co wceq 0re cc0 c1 cA cdiv co cB cdiv co
    ax-apostolmul1 mpan syl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa c1 cA cdiv co cB cdiv co cr wcel c1 cA cdiv co cB cdiv co cc0 cmul co
    cc0 wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co
    cB cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cr wcel cA cc0
    wne wa c1 cA cdiv co cr wcel cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    wa simpl cA rereccl syl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    simprl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprr redivcld c1 cA
    cdiv co cB cdiv co apostoli.6 syl eqtrd cA cB cmul co cc0 wceq cA cB cmul
    co c1 cA cdiv co cB cdiv co cmul co cc0 c1 cA cdiv co cB cdiv co cmul co
    cc0 cA cB cmul co cc0 c1 cA cdiv co cB cdiv co cmul oveq1 eqeq1d syl5ibr
    com12 necon3bd mpd c1 cr wcel cA cB cmul co cr wcel cA cB cmul co cc0 wne
    c1 cA cB cmul co cdiv co cA cB cmul co vx cv cmul co c1 wceq vx cr crio
    wceq 1re vx c1 cA cB cmul co redivval mp3an1 syl2anc eqcomd cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv
    co cmul co c1 wceq cA cB cmul co vx cv cmul co c1 wceq vx cr crio c1 cA
    cdiv co cB cdiv co wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA cB cmul co c1 cA cdiv
    co cB cdiv co cmul co c1 cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa cA cr wcel cB cr wcel c1 cA cdiv co cB cdiv co cr wcel cA cB c1 cA cdiv
    co cB cdiv co cmul co cmul co cA cB cmul co c1 cA cdiv co cB cdiv co cmul
    co wceq cA cr wcel cA cc0 wne cB cr wcel cB cc0 wne wa simpll cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel
    cB cc0 wne wa wa c1 cA cdiv co cB cA cr wcel cA cc0 wne wa cB cr wcel cB
    cc0 wne wa wa cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel cA cc0
    wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel cB
    cc0 wne simprr redivcld cA cB c1 cA cdiv co cB cdiv co ax-apostolmul2
    syl3anc cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB c1 cA
    cdiv co cB cdiv co cmul co cmul co cA c1 cA cdiv co cmul co c1 cA cr wcel
    cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cr wcel cB cr wcel
    cB cc0 wne cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA c1 cA cdiv co
    cmul co wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cr
    wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr wcel cA cc0 wne wa cB cr
    wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel cA cc0 wne wa cB cr wcel
    cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprr c1
    cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a cB c1 cA cdiv co cB cdiv co
    cmul co c1 cA cdiv co cA cmul c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne
    w3a cB c1 cA cdiv co cB cdiv co cmul co c1 c1 cA cdiv co cmul co c1 cA cdiv
    co c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a cB c1 cA cdiv co cB cdiv
    co cmul co cB c1 cB cdiv co c1 cA cdiv co cmul co cmul co cB c1 cB cdiv co
    cmul co c1 cA cdiv co cmul co c1 c1 cA cdiv co cmul co c1 cA cdiv co cr
    wcel cB cr wcel cB cc0 wne w3a c1 cA cdiv co cB cdiv co c1 cB cdiv co c1 cA
    cdiv co cmul co cB cmul c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a c1
    cA cdiv co cB cdiv co c1 cA cdiv co c1 cB cdiv co cmul co c1 cB cdiv co c1
    cA cdiv co cmul co c1 cA cdiv co cB apostoli.9 c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a c1 cA cdiv co cr wcel c1 cB cdiv co cr wcel c1 cA cdiv
    co c1 cB cdiv co cmul co c1 cB cdiv co c1 cA cdiv co cmul co wceq c1 cA
    cdiv co cr wcel cB cr wcel cB cc0 wne simp1 cB cr wcel cB cc0 wne c1 cB
    cdiv co cr wcel c1 cA cdiv co cr wcel cB rereccl 3adant1 c1 cA cdiv co c1
    cB cdiv co ax-apostolmul1 syl2anc eqtrd oveq2d c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a cB cr wcel c1 cB cdiv co cr wcel c1 cA cdiv co cr wcel
    cB c1 cB cdiv co c1 cA cdiv co cmul co cmul co cB c1 cB cdiv co cmul co c1
    cA cdiv co cmul co wceq c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne simp2
    cB cr wcel cB cc0 wne c1 cB cdiv co cr wcel c1 cA cdiv co cr wcel cB
    rereccl 3adant1 c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne simp1 cB c1 cB
    cdiv co c1 cA cdiv co ax-apostolmul2 syl3anc c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a cB c1 cB cdiv co cmul co c1 c1 cA cdiv co cmul cB cr
    wcel cB cc0 wne cB c1 cB cdiv co cmul co c1 wceq c1 cA cdiv co cr wcel cB
    rerecid 3adant1 oveq1d 3eqtrd c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne
    w3a c1 cA cdiv co cr wcel c1 c1 cA cdiv co cmul co c1 cA cdiv co wceq c1 cA
    cdiv co cr wcel cB cr wcel cB cc0 wne simp1 c1 cA cdiv co ax-apostolmul4
    syl eqtrd oveq2d syl3anc cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa cA cr wcel cA cc0 wne wa cA c1 cA cdiv co cmul co c1 wceq cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rerecid syl eqtrd eqtr3d cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cB cdiv co cr
    wcel cA cB cmul co vx cv cmul co c1 wceq vx cr wreu cA cB cmul co c1 cA
    cdiv co cB cdiv co cmul co c1 wceq cA cB cmul co vx cv cmul co c1 wceq vx
    cr crio c1 cA cdiv co cB cdiv co wceq wb cA cr wcel cA cc0 wne wa cB cr
    wcel cB cc0 wne wa wa c1 cA cdiv co cB cA cr wcel cA cc0 wne wa cB cr wcel
    cB cc0 wne wa wa cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr wcel
    cA cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel
    cB cc0 wne simprr redivcld cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    wa wa cA cB cmul co cr wcel cA cB cmul co cc0 wne cA cB cmul co vx cv cmul
    co c1 wceq vx cr wreu cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa
    cA cB cA cr wcel cA cc0 wne cB cr wcel cB cc0 wne wa simpll cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne simprl remulcld cA cr wcel cA cc0 wne wa
    cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv co cmul co
    cc0 wceq wn cA cB cmul co cc0 wne cA cr wcel cA cc0 wne wa cB cr wcel cB
    cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv co cmul co cc0 cA cr wcel
    cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB
    cdiv co cmul co c1 cc0 cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa
    cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA cB cmul co c1 cA cdiv co
    cB cdiv co cmul co c1 cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa
    cA cr wcel cB cr wcel c1 cA cdiv co cB cdiv co cr wcel cA cB c1 cA cdiv co
    cB cdiv co cmul co cmul co cA cB cmul co c1 cA cdiv co cB cdiv co cmul co
    wceq cA cr wcel cA cc0 wne cB cr wcel cB cc0 wne wa simpll cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel
    cB cc0 wne wa wa c1 cA cdiv co cB cA cr wcel cA cc0 wne wa cB cr wcel cB
    cc0 wne wa wa cA cr wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel cA cc0
    wne wa cB cr wcel cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel cB
    cc0 wne simprr redivcld cA cB c1 cA cdiv co cB cdiv co ax-apostolmul2
    syl3anc cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB c1 cA
    cdiv co cB cdiv co cmul co cmul co cA c1 cA cdiv co cmul co c1 cA cr wcel
    cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cr wcel cB cr wcel
    cB cc0 wne cA cB c1 cA cdiv co cB cdiv co cmul co cmul co cA c1 cA cdiv co
    cmul co wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cr
    wcel cA cc0 wne wa c1 cA cdiv co cr wcel cA cr wcel cA cc0 wne wa cB cr
    wcel cB cc0 wne wa simpl cA rereccl syl cA cr wcel cA cc0 wne wa cB cr wcel
    cB cc0 wne simprl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprr c1
    cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a cB c1 cA cdiv co cB cdiv co
    cmul co c1 cA cdiv co cA cmul c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne
    w3a cB c1 cA cdiv co cB cdiv co cmul co c1 c1 cA cdiv co cmul co c1 cA cdiv
    co c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a cB c1 cA cdiv co cB cdiv
    co cmul co cB c1 cB cdiv co c1 cA cdiv co cmul co cmul co cB c1 cB cdiv co
    cmul co c1 cA cdiv co cmul co c1 c1 cA cdiv co cmul co c1 cA cdiv co cr
    wcel cB cr wcel cB cc0 wne w3a c1 cA cdiv co cB cdiv co c1 cB cdiv co c1 cA
    cdiv co cmul co cB cmul c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne w3a c1
    cA cdiv co cB cdiv co c1 cA cdiv co c1 cB cdiv co cmul co c1 cB cdiv co c1
    cA cdiv co cmul co c1 cA cdiv co cB apostoli.9 c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a c1 cA cdiv co cr wcel c1 cB cdiv co cr wcel c1 cA cdiv
    co c1 cB cdiv co cmul co c1 cB cdiv co c1 cA cdiv co cmul co wceq c1 cA
    cdiv co cr wcel cB cr wcel cB cc0 wne simp1 cB cr wcel cB cc0 wne c1 cB
    cdiv co cr wcel c1 cA cdiv co cr wcel cB rereccl 3adant1 c1 cA cdiv co c1
    cB cdiv co ax-apostolmul1 syl2anc eqtrd oveq2d c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a cB cr wcel c1 cB cdiv co cr wcel c1 cA cdiv co cr wcel
    cB c1 cB cdiv co c1 cA cdiv co cmul co cmul co cB c1 cB cdiv co cmul co c1
    cA cdiv co cmul co wceq c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne simp2
    cB cr wcel cB cc0 wne c1 cB cdiv co cr wcel c1 cA cdiv co cr wcel cB
    rereccl 3adant1 c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne simp1 cB c1 cB
    cdiv co c1 cA cdiv co ax-apostolmul2 syl3anc c1 cA cdiv co cr wcel cB cr
    wcel cB cc0 wne w3a cB c1 cB cdiv co cmul co c1 c1 cA cdiv co cmul cB cr
    wcel cB cc0 wne cB c1 cB cdiv co cmul co c1 wceq c1 cA cdiv co cr wcel cB
    rerecid 3adant1 oveq1d 3eqtrd c1 cA cdiv co cr wcel cB cr wcel cB cc0 wne
    w3a c1 cA cdiv co cr wcel c1 c1 cA cdiv co cmul co c1 cA cdiv co wceq c1 cA
    cdiv co cr wcel cB cr wcel cB cc0 wne simp1 c1 cA cdiv co ax-apostolmul4
    syl eqtrd oveq2d syl3anc cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa cA cr wcel cA cc0 wne wa cA c1 cA cdiv co cmul co c1 wceq cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa simpl cA rerecid syl eqtrd eqtr3d c1
    cc0 wne cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa ax-1ne0 a1i
    eqnetrd neneqd cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB
    cmul co c1 cA cdiv co cB cdiv co cmul co cc0 wceq cA cB cmul co cc0 cA cB
    cmul co cc0 wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cB
    cmul co c1 cA cdiv co cB cdiv co cmul co cc0 wceq cA cr wcel cA cc0 wne wa
    cB cr wcel cB cc0 wne wa wa cA cB cmul co c1 cA cdiv co cB cdiv co cmul co
    cc0 wceq cA cB cmul co cc0 wceq cc0 c1 cA cdiv co cB cdiv co cmul co cc0
    wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cc0 c1 cA cdiv co
    cB cdiv co cmul co c1 cA cdiv co cB cdiv co cc0 cmul co cc0 cA cr wcel cA
    cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cB cdiv co cr wcel cc0
    c1 cA cdiv co cB cdiv co cmul co c1 cA cdiv co cB cdiv co cc0 cmul co wceq
    cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co cB cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cr wcel cA cc0 wne wa c1
    cA cdiv co cr wcel cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa simpl
    cA rereccl syl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprl cA cr
    wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprr redivcld cc0 cr wcel c1 cA
    cdiv co cB cdiv co cr wcel cc0 c1 cA cdiv co cB cdiv co cmul co c1 cA cdiv
    co cB cdiv co cc0 cmul co wceq 0re cc0 c1 cA cdiv co cB cdiv co
    ax-apostolmul1 mpan syl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa
    wa c1 cA cdiv co cB cdiv co cr wcel c1 cA cdiv co cB cdiv co cc0 cmul co
    cc0 wceq cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa c1 cA cdiv co
    cB cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne wa wa cA cr wcel cA cc0
    wne wa c1 cA cdiv co cr wcel cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    wa simpl cA rereccl syl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne
    simprl cA cr wcel cA cc0 wne wa cB cr wcel cB cc0 wne simprr redivcld c1 cA
    cdiv co cB cdiv co apostoli.6 syl eqtrd cA cB cmul co cc0 wceq cA cB cmul
    co c1 cA cdiv co cB cdiv co cmul co cc0 c1 cA cdiv co cB cdiv co cmul co
    cc0 cA cB cmul co cc0 c1 cA cdiv co cB cdiv co cmul oveq1 eqeq1d syl5ibr
    com12 necon3bd mpd c1 cr wcel cA cB cmul co cr wcel cA cB cmul co cc0 wne
    cA cB cmul co vx cv cmul co c1 wceq vx cr wreu 1re vx c1 cA cB cmul co
    apostoli.8 mp3an1 syl2anc cA cB cmul co vx cv cmul co c1 wceq cA cB cmul co
    c1 cA cdiv co cB cdiv co cmul co c1 wceq vx cr c1 cA cdiv co cB cdiv co vx
    cv c1 cA cdiv co cB cdiv co wceq cA cB cmul co vx cv cmul co cA cB cmul co
    c1 cA cdiv co cB cdiv co cmul co c1 vx cv c1 cA cdiv co cB cdiv co cA cB
    cmul co cmul oveq2 eqeq1d riota2 syl2anc mpbid eqtr3d eqcomd $.
$}

${
  $d x A $. $d x B $.

  apostoli.13 $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( ( C e. RR /\ C =/= 0 ) /\ ( D e. RR /\ D =/= 0 ) ) ) -> ( ( A / C ) + ( B / D ) ) = ( ( ( A x. D ) + ( B x. C ) ) / ( C x. D ) ) ) $=
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa wa cA cC cdiv co cB cD cdiv co caddc co cA cD cmul co cB cC cmul co
    caddc co c1 cC cD cmul co cdiv co cmul co cA cD cmul co cB cC cmul co caddc
    co cC cD cmul co cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa wa c1 cC cD cmul co cdiv co cA cD cmul co cB cC
    cmul co caddc co cmul co cA cC cdiv co cB cD cdiv co caddc co cA cD cmul co
    cB cC cmul co caddc co c1 cC cD cmul co cdiv co cmul co cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cD
    cmul co cdiv co cA cD cmul co cB cC cmul co caddc co cmul co c1 cC cD cmul
    co cdiv co cA cD cmul co cmul co c1 cC cD cmul co cdiv co cB cC cmul co
    cmul co caddc co cA cC cdiv co cB cD cdiv co caddc co cA cr wcel cB cr wcel
    wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cD cmul co
    cdiv co cr wcel cA cD cmul co cr wcel cB cC cmul co cr wcel c1 cC cD cmul
    co cdiv co cA cD cmul co cB cC cmul co caddc co cmul co c1 cC cD cmul co
    cdiv co cA cD cmul co cmul co c1 cC cD cmul co cdiv co cB cC cmul co cmul
    co caddc co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co c1 cC cD cmul co cdiv co
    cr cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    wa wa wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa c1 cC cdiv co cD
    cdiv co c1 cC cD cmul co cdiv co wceq cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprr cC cD rerecdiv2
    syl2anc cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa c1 cC cdiv co cD cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne wa c1 cC cdiv
    co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa simprl cC rereccl syl cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne simprrl cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne simprrr redivcld eqeltrrd cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cD cA cr
    wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    simprrl remulcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa cB cC cA cr wcel cB cr wcel cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa simplr cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne cD cr wcel cD cc0 wne wa simprll remulcld c1 cC cD cmul co cdiv
    co cA cD cmul co cB cC cmul co ax-apostol3 syl3anc cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cD cmul co
    cdiv co cA cD cmul co cmul co cA cC cdiv co c1 cC cD cmul co cdiv co cB cC
    cmul co cmul co cB cD cdiv co caddc cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co cD cA
    cmul co cmul co c1 cC cD cmul co cdiv co cA cD cmul co cmul co cA cC cdiv
    co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    wa wa wa c1 cC cdiv co cD cdiv co cD cA cmul co cmul co c1 cC cD cmul co
    cdiv co cD cA cmul co cmul co c1 cC cD cmul co cdiv co cA cD cmul co cmul
    co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    wa wa wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa c1 cC cdiv co cD
    cdiv co cD cA cmul co cmul co c1 cC cD cmul co cdiv co cD cA cmul co cmul
    co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa simprl cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa simprr cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa
    c1 cC cdiv co cD cdiv co c1 cC cD cmul co cdiv co cD cA cmul co cmul cC cD
    rerecdiv2 oveq1d syl2anc cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa wa cA cr wcel cD cr wcel c1 cC cD cmul co cdiv
    co cA cD cmul co cmul co c1 cC cD cmul co cdiv co cD cA cmul co cmul co
    wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    wa wa simpll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne simprrl cA cr wcel cD cr wcel wa cA cD cmul co cD cA cmul co c1
    cC cD cmul co cdiv co cmul cA cD axapostolmul1 oveq2d syl2anc eqtr4d cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    c1 cC cdiv co cD cdiv co cD cA cmul co cmul co c1 cC cdiv co cD cdiv co cD
    cmul co cA cmul co cA cC cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co cr wcel cD
    cr wcel cA cr wcel c1 cC cdiv co cD cdiv co cD cA cmul co cmul co c1 cC
    cdiv co cD cdiv co cD cmul co cA cmul co wceq cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    cC cr wcel cC cc0 wne wa c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cC rereccl syl cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    simprrr redivcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne simprrl cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD
    cr wcel cD cc0 wne wa wa simpll c1 cC cdiv co cD cdiv co cD cA
    axapostolmul2 syl3anc cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD
    cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co cD cmul co cA cmul co
    cA c1 cC cdiv co cmul co cA cC cdiv co cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co cD
    cmul co cA cmul co c1 cC cdiv co cA cmul co cA c1 cC cdiv co cmul co cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    c1 cC cdiv co cD cdiv co cD cmul co c1 cC cdiv co cA cmul cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv
    co cD cdiv co cD cmul co c1 cC cdiv co c1 cmul co c1 c1 cC cdiv co cmul co
    c1 cC cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co cD cmul co c1 cC cdiv co c1 cD
    cdiv co cD cmul co cmul co c1 cC cdiv co cD c1 cD cdiv co cmul co cmul co
    c1 cC cdiv co c1 cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co cD cmul co c1 cC
    cdiv co c1 cD cdiv co cmul co cD cmul co c1 cC cdiv co c1 cD cdiv co cD
    cmul co cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa c1 cC cdiv co cr wcel cD cr wcel cD cc0 wne c1 cC
    cdiv co cD cdiv co cD cmul co c1 cC cdiv co c1 cD cdiv co cmul co cD cmul
    co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa cC cr wcel cC cc0 wne wa c1 cC cdiv co cr wcel cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cC
    rereccl syl cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne simprrl cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne simprrr c1 cC cdiv co cr wcel cD cr wcel cD cc0 wne w3a c1
    cC cdiv co cD cdiv co c1 cC cdiv co c1 cD cdiv co cmul co cD cmul c1 cC
    cdiv co cD apostoli.9 oveq1d syl3anc cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cr wcel c1 cD cdiv
    co cr wcel cD cr wcel c1 cC cdiv co c1 cD cdiv co cD cmul co cmul co c1 cC
    cdiv co c1 cD cdiv co cmul co cD cmul co wceq cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne
    wa c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa simprl cC rereccl syl cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr wcel cD cc0 wne
    wa c1 cD cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa simprr cD rereccl syl cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl c1 cC cdiv co c1 cD
    cdiv co cD axapostolmul2 syl3anc eqtr4d cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr wcel c1 cD cdiv co cr
    wcel c1 cC cdiv co cD c1 cD cdiv co cmul co cmul co c1 cC cdiv co c1 cD
    cdiv co cD cmul co cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne simprrl cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr wcel cD cc0 wne wa c1 cD
    cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa simprr cD rereccl syl cD cr wcel c1 cD cdiv co cr wcel
    wa cD c1 cD cdiv co cmul co c1 cD cdiv co cD cmul co c1 cC cdiv co cmul cD
    c1 cD cdiv co axapostolmul1 oveq2d syl2anc cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr wcel cD cc0 wne c1
    cC cdiv co cD c1 cD cdiv co cmul co cmul co c1 cC cdiv co c1 cmul co wceq
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    simprrl cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne simprrr cD cr wcel cD cc0 wne wa cD c1 cD cdiv co cmul co c1 c1 cC cdiv
    co cmul cD rerecid oveq2d syl2anc 3eqtr2d cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cr wcel c1
    cr wcel c1 cC cdiv co c1 cmul co c1 c1 cC cdiv co cmul co wceq cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr
    wcel cC cc0 wne wa c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cC rereccl syl c1 cr
    wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa 1re a1i c1 cC cdiv co c1 axapostolmul1 syl2anc cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC
    cdiv co cr wcel c1 c1 cC cdiv co cmul co c1 cC cdiv co wceq cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr
    wcel cC cc0 wne wa c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cC rereccl syl c1 cC
    cdiv co axapostolmul4 syl 3eqtrd oveq1d cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cr wcel cA cr
    wcel c1 cC cdiv co cA cmul co cA c1 cC cdiv co cmul co wceq cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr
    wcel cC cc0 wne wa c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cC rereccl syl cA cr
    wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll
    c1 cC cdiv co cA axapostolmul1 syl2anc eqtrd cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cr wcel cC cr wcel cC
    cc0 wne cA cC cdiv co cA c1 cC cdiv co cmul co wceq cA cr wcel cB cr wcel
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprlr
    cA cC apostoli.9 syl3anc eqtr4d eqtrd eqtr3d cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cC cdiv co
    cC cB cmul co cmul co c1 cC cD cmul co cdiv co cB cC cmul co cmul co cB cD
    cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa c1 cD cdiv co cC cdiv co cC cB cmul co cmul co c1 cD cC cmul
    co cdiv co cC cB cmul co cmul co c1 cC cD cmul co cdiv co cB cC cmul co
    cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa cD cr wcel cD cc0 wne wa cC cr wcel cC cc0 wne wa c1 cD cdiv
    co cC cdiv co cC cB cmul co cmul co c1 cD cC cmul co cdiv co cC cB cmul co
    cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa simprr cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD
    cr wcel cD cc0 wne wa simprl cD cr wcel cD cc0 wne wa cC cr wcel cC cc0 wne
    wa wa c1 cD cdiv co cC cdiv co c1 cD cC cmul co cdiv co cC cB cmul co cmul
    cD cC rerecdiv2 oveq1d syl2anc cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cD cmul co cdiv co cB cC cmul
    co cmul co c1 cC cD cmul co cdiv co cC cB cmul co cmul co c1 cD cC cmul co
    cdiv co cC cB cmul co cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa cB cr wcel cC cr wcel c1 cC cD cmul
    co cdiv co cB cC cmul co cmul co c1 cC cD cmul co cdiv co cC cB cmul co
    cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa simplr cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr
    wcel cD cc0 wne wa simprll cB cr wcel cC cr wcel wa cB cC cmul co cC cB
    cmul co c1 cC cD cmul co cdiv co cmul cB cC axapostolmul1 oveq2d syl2anc cA
    cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa
    wa cC cr wcel cD cr wcel c1 cC cD cmul co cdiv co cC cB cmul co cmul co c1
    cD cC cmul co cdiv co cC cB cmul co cmul co wceq cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl cC cr wcel
    cD cr wcel wa c1 cC cD cmul co cdiv co c1 cD cC cmul co cdiv co cC cB cmul
    co cmul cC cr wcel cD cr wcel wa cC cD cmul co cD cC cmul co c1 cdiv cC cD
    axapostolmul1 oveq2d oveq1d syl2anc eqtrd eqtr4d cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cC
    cdiv co cC cB cmul co cmul co c1 cD cdiv co cC cdiv co cC cmul co cB cmul
    co cB cD cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa c1 cD cdiv co cC cdiv co cr wcel cC cr wcel cB cr
    wcel c1 cD cdiv co cC cdiv co cC cB cmul co cmul co c1 cD cdiv co cC cdiv
    co cC cmul co cB cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cC cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr wcel
    cD cc0 wne wa c1 cD cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa simprr cD rereccl syl cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprlr
    redivcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0
    wne wa simprll cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa simplr c1 cD cdiv co cC cdiv co cC cB axapostolmul2 syl3anc
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa wa c1 cD cdiv co cC cdiv co cC cmul co cB cmul co cB c1 cD cdiv co cmul
    co cB cD cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa c1 cD cdiv co cC cdiv co cC cmul co cB cmul co c1
    cD cdiv co cB cmul co cB c1 cD cdiv co cmul co cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cC cdiv
    co cC cmul co c1 cD cdiv co cB cmul cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cC cdiv co cC cmul
    co c1 cD cdiv co c1 cmul co c1 c1 cD cdiv co cmul co c1 cD cdiv co cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    c1 cD cdiv co cC cdiv co cC cmul co c1 cD cdiv co c1 cC cdiv co cC cmul co
    cmul co c1 cD cdiv co cC c1 cC cdiv co cmul co cmul co c1 cD cdiv co c1
    cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa c1 cD cdiv co cC cdiv co cC cmul co c1 cD cdiv co c1 cC cdiv
    co cmul co cC cmul co c1 cD cdiv co c1 cC cdiv co cC cmul co cmul co cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    c1 cD cdiv co cr wcel cC cr wcel cC cc0 wne c1 cD cdiv co cC cdiv co cC
    cmul co c1 cD cdiv co c1 cC cdiv co cmul co cC cmul co wceq cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr
    wcel cD cc0 wne wa c1 cD cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprr cD rereccl syl cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa
    simprlr c1 cD cdiv co cr wcel cC cr wcel cC cc0 wne w3a c1 cD cdiv co cC
    cdiv co c1 cD cdiv co c1 cC cdiv co cmul co cC cmul c1 cD cdiv co cC
    apostoli.9 oveq1d syl3anc cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cr wcel c1 cC cdiv co cr wcel
    cC cr wcel c1 cD cdiv co c1 cC cdiv co cC cmul co cmul co c1 cD cdiv co c1
    cC cdiv co cmul co cC cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr wcel cD cc0 wne wa c1 cD
    cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa simprr cD rereccl syl cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne wa
    c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD
    cr wcel cD cc0 wne wa simprl cC rereccl syl cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll c1 cD cdiv co c1 cC cdiv
    co cC axapostolmul2 syl3anc eqtr4d cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel c1 cC cdiv co cr wcel
    c1 cD cdiv co cC c1 cC cdiv co cmul co cmul co c1 cD cdiv co c1 cC cdiv co
    cC cmul co cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD
    cr wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne wa c1 cC cdiv
    co cr wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa simprl cC rereccl syl cC cr wcel c1 cC cdiv co cr wcel wa cC c1
    cC cdiv co cmul co c1 cC cdiv co cC cmul co c1 cD cdiv co cmul cC c1 cC
    cdiv co axapostolmul1 oveq2d syl2anc cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne c1 cD cdiv
    co cC c1 cC cdiv co cmul co cmul co c1 cD cdiv co c1 cmul co wceq cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa
    simprlr cC cr wcel cC cc0 wne wa cC c1 cC cdiv co cmul co c1 c1 cD cdiv co
    cmul cC rerecid oveq2d syl2anc 3eqtr2d cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cr wcel c1 cr
    wcel c1 cD cdiv co c1 cmul co c1 c1 cD cdiv co cmul co wceq cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr
    wcel cD cc0 wne wa c1 cD cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprr cD rereccl syl c1 cr
    wcel cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa 1re a1i c1 cD cdiv co c1 axapostolmul1 syl2anc cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD
    cdiv co cr wcel c1 c1 cD cdiv co cmul co c1 cD cdiv co wceq cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr
    wcel cD cc0 wne wa c1 cD cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprr cD rereccl syl c1 cD
    cdiv co axapostolmul4 syl 3eqtrd oveq1d cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cD cdiv co cr wcel cB cr
    wcel c1 cD cdiv co cB cmul co cB c1 cD cdiv co cmul co wceq cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cr
    wcel cD cc0 wne wa c1 cD cdiv co cr wcel cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprr cD rereccl syl cA cr
    wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr
    c1 cD cdiv co cB axapostolmul1 syl2anc eqtrd cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cB cr wcel cD cr wcel cD
    cc0 wne cB cD cdiv co cB c1 cD cdiv co cmul co wceq cA cr wcel cB cr wcel
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrr
    cB cD apostoli.9 syl3anc eqtr4d eqtrd eqtr3d oveq12d eqtrd cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cD
    cmul co cdiv co cr wcel cA cD cmul co cB cC cmul co caddc co cr wcel c1 cC
    cD cmul co cdiv co cA cD cmul co cB cC cmul co caddc co cmul co cA cD cmul
    co cB cC cmul co caddc co c1 cC cD cmul co cdiv co cmul co wceq cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC
    cdiv co cD cdiv co c1 cC cD cmul co cdiv co cr cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa c1 cC cdiv co cD cdiv co c1 cC cD cmul co cdiv
    co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa simprl cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa simprr cC cD rerecdiv2 syl2anc cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    cC cr wcel cC cc0 wne wa c1 cC cdiv co cr wcel cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa simprl cC rereccl syl cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    simprrr redivcld eqeltrrd cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa wa cA cD cmul co cB cC cmul co cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cD cA cr
    wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    simprrl remulcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa cB cC cA cr wcel cB cr wcel cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa simplr cA cr wcel cB cr wcel wa cC cr wcel
    cC cc0 wne cD cr wcel cD cc0 wne wa simprll remulcld readdcld c1 cC cD cmul
    co cdiv co cA cD cmul co cB cC cmul co caddc co axapostolmul1 syl2anc
    eqtr3d cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa cA cD cmul co cB cC cmul co caddc co cr wcel cC cD cmul co cr
    wcel cC cD cmul co cc0 wne cA cD cmul co cB cC cmul co caddc co cC cD cmul
    co cdiv co cA cD cmul co cB cC cmul co caddc co c1 cC cD cmul co cdiv co
    cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa wa wa cA cD cmul co cB cC cmul co cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cD cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl
    remulcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa wa cB cC cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa simplr cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    cD cr wcel cD cc0 wne wa simprll remulcld readdcld cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cD cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl
    remulcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa wa cC cD cmul co cc0 cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cD cmul co cc0 wceq wn cC cc0
    wceq cD cc0 wceq wo wn cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD
    cr wcel cD cc0 wne wa wa wa cC cc0 wceq wn cD cc0 wceq wn wa cC cc0 wceq cD
    cc0 wceq wo wn cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa wa wa cC cc0 wceq wn cD cc0 wceq wn cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cc0 cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprlr neneqd
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa wa cD cc0 cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne simprrr neneqd jca cC cc0 wceq cD cc0 wceq ioran sylibr cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    cC cD cmul co cc0 wceq cC cc0 wceq cD cc0 wceq wo cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cD cr
    wcel cC cD cmul co cc0 wceq cC cc0 wceq cD cc0 wceq wo wb cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl cC cD
    apostoli.11 syl2anc notbid mpbird neqned cA cD cmul co cB cC cmul co caddc
    co cC cD cmul co apostoli.9 syl3anc eqtr4d $.
$}

${
  apostoli.14 $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( ( C e. RR /\ C =/= 0 ) /\ ( D e. RR /\ D =/= 0 ) ) ) -> ( ( A / C ) x. ( B / D ) ) = ( ( A x. B ) / ( C x. D ) ) ) $=
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa wa cA cC cdiv co cB cD cdiv co cmul co cA cB cmul co c1 cC cdiv co c1 cD
    cdiv co cmul co cmul co cA cB cmul co cC cD cmul co cdiv co cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cC
    cdiv co cB cD cdiv co cmul co c1 cC cdiv co cA cmul co cB cmul co c1 cD
    cdiv co cmul co cA cB cmul co c1 cC cdiv co c1 cD cdiv co cmul co cmul co
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa wa cA cC cdiv co cB cD cdiv co cmul co c1 cC cdiv co cA cmul co cB c1 cD
    cdiv co cmul co cmul co c1 cC cdiv co cA cmul co cB cmul co c1 cD cdiv co
    cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa cA cC cdiv co c1 cC cdiv co cA cmul co cB cD cdiv co cB c1 cD
    cdiv co cmul co cmul cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD
    cr wcel cD cc0 wne wa wa wa cA cC cdiv co cA c1 cC cdiv co cmul co c1 cC
    cdiv co cA cmul co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa cA cr wcel cC cr wcel cC cc0 wne cA cC cdiv co cA
    c1 cC cdiv co cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa simpll cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprlr cA cC apostoli.9 syl3anc
    cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa wa cA cr wcel c1 cC cdiv co cr wcel cA c1 cC cdiv co cmul co c1 cC cdiv
    co cA cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa simpll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa wa cC cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprlr rereccld cA c1 cC cdiv co
    ax-apostolmul1 syl2anc eqtrd cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa wa cB cr wcel cD cr wcel cD cc0 wne cB cD
    cdiv co cB c1 cD cdiv co cmul co wceq cA cr wcel cB cr wcel cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl cA cr wcel cB cr wcel
    wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrr cB cD apostoli.9
    syl3anc oveq12d cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa c1 cC cdiv co cA cmul co cr wcel cB cr wcel c1 cD
    cdiv co cr wcel c1 cC cdiv co cA cmul co cB c1 cD cdiv co cmul co cmul co
    c1 cC cdiv co cA cmul co cB cmul co c1 cD cdiv co cmul co wceq cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC
    cdiv co cA cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa wa cC cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr
    wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    cD cr wcel cD cc0 wne wa simprlr rereccld cA cr wcel cB cr wcel cC cr wcel
    cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll remulcld cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cA
    cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    simprrl cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne simprrr rereccld c1 cC cdiv co cA cmul co cB c1 cD cdiv co
    ax-apostolmul2 syl3anc eqtrd cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa wa cA cB cmul co c1 cC cdiv co c1 cD cdiv co
    cmul co cmul co cA cB cmul co c1 cC cdiv co cmul co c1 cD cdiv co cmul co
    c1 cC cdiv co cA cmul co cB cmul co c1 cD cdiv co cmul co cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cB cmul
    co cr wcel c1 cC cdiv co cr wcel c1 cD cdiv co cr wcel cA cB cmul co c1 cC
    cdiv co c1 cD cdiv co cmul co cmul co cA cB cmul co c1 cC cdiv co cmul co
    c1 cD cdiv co cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa wa cA cB cA cr wcel cB cr wcel cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll cA cr wcel cB cr wcel cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr remulcld cA cr wcel
    cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cA
    cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa
    simprll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0
    wne wa simprlr rereccld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa
    cD cr wcel cD cc0 wne wa wa wa cD cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne simprrl cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrr rereccld cA cB cmul co c1
    cC cdiv co c1 cD cdiv co ax-apostolmul2 syl3anc cA cr wcel cB cr wcel wa cC
    cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cB cmul co c1 cC
    cdiv co cmul co c1 cC cdiv co cA cmul co cB cmul co c1 cD cdiv co cmul cA
    cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa
    wa c1 cC cdiv co cA cB cmul co cmul co cA cB cmul co c1 cC cdiv co cmul co
    c1 cC cdiv co cA cmul co cB cmul co cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cr wcel cA cB cmul
    co cr wcel c1 cC cdiv co cA cB cmul co cmul co cA cB cmul co c1 cC cdiv co
    cmul co wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel
    cD cc0 wne wa wa wa cC cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr
    wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    cD cr wcel cD cc0 wne wa simprlr rereccld cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cB cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll cA cr wcel
    cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr
    remulcld c1 cC cdiv co cA cB cmul co ax-apostolmul1 syl2anc cA cr wcel cB
    cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC
    cdiv co cr wcel cA cr wcel cB cr wcel c1 cC cdiv co cA cB cmul co cmul co
    c1 cC cdiv co cA cmul co cB cmul co wceq cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cA cr wcel cB cr wcel
    wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprlr rereccld cA
    cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa
    simpll cA cr wcel cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne
    wa wa simplr c1 cC cdiv co cA cB ax-apostolmul2 syl3anc eqtr3d oveq1d eqtrd
    eqtr4d cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa cA cB cmul co c1 cC cdiv co c1 cD cdiv co cmul co cmul co cA
    cB cmul co c1 cC cD cmul co cdiv co cmul co cA cB cmul co cC cD cmul co
    cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa c1 cC cdiv co c1 cD cdiv co cmul co c1 cC cD cmul co cdiv co
    cA cB cmul co cmul cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa c1 cC cdiv co cD cdiv co c1 cC cdiv co c1 cD cdiv
    co cmul co c1 cC cD cmul co cdiv co cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa c1 cC cdiv co cr wcel cD cr wcel
    cD cc0 wne c1 cC cdiv co cD cdiv co c1 cC cdiv co c1 cD cdiv co cmul co
    wceq cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0
    wne wa wa wa cC cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr wcel
    cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr
    wcel cD cc0 wne wa simprlr rereccld cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne simprrl cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrr c1 cC cdiv co cD
    apostoli.9 syl3anc cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr
    wcel cD cc0 wne wa wa wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa
    wa c1 cC cdiv co cD cdiv co c1 cC cD cmul co cdiv co wceq cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpr cC cD
    rerecdiv2 syl eqtr3d oveq2d cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne wa wa wa cA cB cmul co cr wcel cC cD cmul co cr
    wcel cC cD cmul co cc0 wne cA cB cmul co cC cD cmul co cdiv co cA cB cmul
    co c1 cC cD cmul co cdiv co cmul co wceq cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cA cB cA cr wcel cB cr
    wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simpll cA cr wcel
    cB cr wcel cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa simplr
    remulcld cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa wa cC cD cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD cr
    wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne
    wa cD cr wcel cD cc0 wne simprrl remulcld cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cD cmul co cc0 cA cr
    wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa
    cC cD cmul co cc0 wceq wn cC cc0 wceq cD cc0 wceq wo wn cA cr wcel cB cr
    wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cc0 wceq
    wn cD cc0 wceq wn wa cC cc0 wceq cD cc0 wceq wo wn cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cC cc0 wceq wn cD
    cc0 wceq wn cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne wa cD cr wcel cD
    cc0 wne wa wa wa cC cc0 cA cr wcel cB cr wcel wa cC cr wcel cC cc0 wne cD
    cr wcel cD cc0 wne wa simprlr neneqd cA cr wcel cB cr wcel wa cC cr wcel cC
    cc0 wne wa cD cr wcel cD cc0 wne wa wa wa cD cc0 cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrr neneqd jca cC cc0
    wceq cD cc0 wceq ioran sylibr cA cr wcel cB cr wcel wa cC cr wcel cC cc0
    wne wa cD cr wcel cD cc0 wne wa wa wa cC cr wcel cD cr wcel cC cD cmul co
    cc0 wceq wn cC cc0 wceq cD cc0 wceq wo wn wb cA cr wcel cB cr wcel wa cC cr
    wcel cC cc0 wne cD cr wcel cD cc0 wne wa simprll cA cr wcel cB cr wcel wa
    cC cr wcel cC cc0 wne wa cD cr wcel cD cc0 wne simprrl cC cr wcel cD cr
    wcel wa cC cD cmul co cc0 wceq cC cc0 wceq cD cc0 wceq wo cC cD apostoli.11
    notbid syl2anc mpbird neqned cA cB cmul co cC cD cmul co apostoli.9 syl3anc
    eqtr4d eqtrd $.
$}
