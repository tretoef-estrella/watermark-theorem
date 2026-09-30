import RequestProject.Watermark.Defs
open Matrix Watermark
namespace T5


/-- Certificate for `m = 5`: the rows of a `75 × 26` matrix `B`, written in base `5`
(digit `k` of row `i` is the entry `(i, k)`). -/
def fiveB : List ℕ :=
  [59608460939457032,
    19079599625786,
    11920959521563306,
    2479705810938406,
    298500823974610781,
    763186037501,
    11924744883315630,
    2403265430253150,
    298500091553612625,
    59700164795410000,
    12016449281253126,
    2384948800796880,
    298503877062578150,
    59623724426172000,
    30578125625,
    2384216798831251,
    298595581308609380,
    59605408007890650,
    3816162500125,
    11940008789063125,
    298519140871096876,
    59604675302750005,
    95520068437525,
    11921691894922000,
    2388001708985000,
    573159228531251,
    61992841796953130,
    309963447510156275,
    343019531375,
    190439456875,
    62108613291019375,
    309971624804703126,
    42755127031255,
    23803955468775,
    500488283203250,
    310135651857422000,
    99188242191250,
    114471484390626,
    572357177812505,
    62084198242578150,
    96131836328150,
    3820802734500,
    495941171878750,
    61988983203140626,
    309944152832109380,
    96131591875005,
    480658203515650,
    62007934572265750,
    309944305429691250,
    48843751,
    74863435107813125,
    315190130869218875,
    26802093507828150,
    14801177978518755,
    14781951904296876,
    417710119628906251,
    658134491016016250,
    369568023935625125,
    357627868654312525,
    357627869873050005,
    60180694580081255,
    300426635742187501,
    11920929004297500,
    1474687625,
    769044937525,
    60100708009781275,
    300407409667971880,
    11920930175781251,
    769092188125,
    99212900468875,
    60081482187578250,
    300407410890640650,
    11921697998050005,
    99212646484376,
    19226123438125]

/-- Certificate for `m = 5`: the rows of a `26 × 75` matrix `C` with `Ḡ = B C`. -/
def fiveC : List ℕ :=
  [25145866969569830029513514164253324270726014406250001,
    20190778061250791464307490214938484400417049562500005,
    25882059288544256878786340634920820841001608888671900,
    6775998217953471733175348155899159868891771242187625,
    23576740189317135807889788776985556021327978517578750,
    18719965267470595282349911388475447999932419441409375,
    25611731807935467260515683447010815178917719734390625,
    8968306849426044298064670614316128298371440437578125,
    19814903787142435023167903856723569473768026131250000,
    21034164870336002956332234579487703856870594492187500,
    23879957965322751224195870791096240425610061083984375,
    19649900095481076525917351101408712663725290771484375,
    16487939796458461759947409271262586414742462158203125,
    6083221709071906513600379840820841789245605468750000,
    26186750302893835336902963843080961704254150390625000,
    10049850669234672379940299493843510746955871582031250,
    17234966376060612049033414589474759995937347412109375,
    9813082130237749183892335409881547093391418457031250,
    12185934814376719889439394393358379602432250976562500,
    24320979889247651471753128077625297009944915771484375,
    26465545791345967985300542294862680137157440185546875,
    25173509586175380015049540816107764840126037597656250,
    19035937503193845365956349269254133105278015136718750,
    2326188525074526225466797768604010343551635742187500,
    18248285003346076393881958210840821266174316406250000,
    8221073224035091442374323378317058086395263671875000]


/-- Certificate for `m = 5`: the rows of a `75 × 26` matrix `Y`, a right inverse of 26 rows
of `Ḡ`. -/
def fiveY : List ℕ :=
  [18151558557443345,
    369178075910527969,
    1007467553586579768,
    570536692977959841,
    1080955758471238199,
    852408472258710266,
    373020868305618666,
    933989600318691595,
    662290740519960402,
    0,
    1291783161129567406,
    692898329511560691,
    1471052776355817824,
    0,
    0,
    1481898471020882493,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    422098793419532996,
    975799525222419576,
    678234977901283285,
    823073757159763728,
    0,
    617370512356494196,
    886474328756182163,
    159383844993549001,
    0,
    0,
    1027414741945184105,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    562190466835428948,
    1273180538674711822,
    27348975767831601,
    0,
    0,
    1256233713342218030,
    546751027811586455,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

/-- The index `25 j + 5 k + l` of a line `(j, k, l)`. -/
def lineIdx (p : Line 5) : ℕ := p.1.val * 25 + p.2.1.val * 5 + p.2.2.val

/-- Digit `k` of row `i` of a certificate. -/
def digit (L : List ℕ) (i k : ℕ) : ZMod 5 := ((L.getD i 0 / 5 ^ k % 5 : ℕ) : ZMod 5)

/-- The certificate matrix `B`. -/
def matB : Matrix (Line 5) (Fin 26) (ZMod 5) := Matrix.of fun p k => digit fiveB (lineIdx p) k

/-- The certificate matrix `C`. -/
def matC : Matrix (Fin 26) (Line 5) (ZMod 5) := Matrix.of fun k p => digit fiveC k (lineIdx p)

/-- The certificate matrix `Y`. -/
def matY : Matrix (Line 5) (Fin 26) (ZMod 5) := Matrix.of fun p k => digit fiveY (lineIdx p) k

set_option maxRecDepth 100000 in
theorem hBC_0_0 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨0, by decide⟩ : Fin 3), (0 : ZMod 5), b) q =
      (matB * matC) ((⟨0, by decide⟩ : Fin 3), (0 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_0_1 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨0, by decide⟩ : Fin 3), (1 : ZMod 5), b) q =
      (matB * matC) ((⟨0, by decide⟩ : Fin 3), (1 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_0_2 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨0, by decide⟩ : Fin 3), (2 : ZMod 5), b) q =
      (matB * matC) ((⟨0, by decide⟩ : Fin 3), (2 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_0_3 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨0, by decide⟩ : Fin 3), (3 : ZMod 5), b) q =
      (matB * matC) ((⟨0, by decide⟩ : Fin 3), (3 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_0_4 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨0, by decide⟩ : Fin 3), (4 : ZMod 5), b) q =
      (matB * matC) ((⟨0, by decide⟩ : Fin 3), (4 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_1_0 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨1, by decide⟩ : Fin 3), (0 : ZMod 5), b) q =
      (matB * matC) ((⟨1, by decide⟩ : Fin 3), (0 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_1_1 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨1, by decide⟩ : Fin 3), (1 : ZMod 5), b) q =
      (matB * matC) ((⟨1, by decide⟩ : Fin 3), (1 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_1_2 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨1, by decide⟩ : Fin 3), (2 : ZMod 5), b) q =
      (matB * matC) ((⟨1, by decide⟩ : Fin 3), (2 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_1_3 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨1, by decide⟩ : Fin 3), (3 : ZMod 5), b) q =
      (matB * matC) ((⟨1, by decide⟩ : Fin 3), (3 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_1_4 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨1, by decide⟩ : Fin 3), (4 : ZMod 5), b) q =
      (matB * matC) ((⟨1, by decide⟩ : Fin 3), (4 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_2_0 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨2, by decide⟩ : Fin 3), (0 : ZMod 5), b) q =
      (matB * matC) ((⟨2, by decide⟩ : Fin 3), (0 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_2_1 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨2, by decide⟩ : Fin 3), (1 : ZMod 5), b) q =
      (matB * matC) ((⟨2, by decide⟩ : Fin 3), (1 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_2_2 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨2, by decide⟩ : Fin 3), (2 : ZMod 5), b) q =
      (matB * matC) ((⟨2, by decide⟩ : Fin 3), (2 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_2_3 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨2, by decide⟩ : Fin 3), (3 : ZMod 5), b) q =
      (matB * matC) ((⟨2, by decide⟩ : Fin 3), (3 : ZMod 5), b) q := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hBC_2_4 : ∀ b : ZMod 5, ∀ q : Line 5,
    (gram 5).map (Int.castRingHom (ZMod 5)) ((⟨2, by decide⟩ : Fin 3), (4 : ZMod 5), b) q =
      (matB * matC) ((⟨2, by decide⟩ : Fin 3), (4 : ZMod 5), b) q := by
  decide +kernel

theorem hBC : (gram 5).map (Int.castRingHom (ZMod 5)) = matB * matC := by
  ext ⟨j, a, b⟩ q
  fin_cases j <;> fin_cases a <;> first | exact hBC_0_0 b q | exact hBC_0_1 b q | exact hBC_0_2 b q | exact hBC_0_3 b q | exact hBC_0_4 b q | exact hBC_1_0 b q | exact hBC_1_1 b q | exact hBC_1_2 b q | exact hBC_1_3 b q | exact hBC_1_4 b q | exact hBC_2_0 b q | exact hBC_2_1 b q | exact hBC_2_2 b q | exact hBC_2_3 b q | exact hBC_2_4 b q
end T5
