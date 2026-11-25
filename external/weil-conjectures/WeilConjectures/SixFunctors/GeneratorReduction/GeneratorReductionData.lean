/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-! # Canonical coefficient squares for the basic six-functor generators

Source: blueprint fix-prop-coherence, basic structural maps
(blueprint: lem-sf-generator-reduction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures

/-! The integral direct-image tower used by the generator statement.  This
construction belongs to the owning item module: the recorded
`prose-03-02` node keeps its landed common-stage declaration,
while this item needs the simultaneous strict-system specialization below. -/

/-- The integral direct image is the total limit of the actual strict quotient
system's total right-derived direct image.
Source: blueprint main-20261015, def:weil-direct-image-object, integral paragraph;
coherence proof, step 2 (blueprint: lem-sf-generator-reduction-coherence). -/
def integralSystemDerivedDirectImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : IntegralSystemRealization.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (IntegralSystemRealization.calculus l E X).reduction ⋙
    IntegralSystemRealization.Operations.push l E o f ⋙ coefficientSequenceLimit l E Y

end WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

/-- Presentations of the actual system and ordinary ringed-site operations.
Each comparison is fixed by the recorded section, total-complex or adjunction
normalization; there are no generator arrow fields.
Source: blueprint coherence proof, steps 1--5
(blueprint: lem-sf-generator-reduction-coherence). -/
structure Operations where
  system : IntegralSystemRealization.Operations l E
  composition : IntegralSystemRealization.Compositors l E system
  opens : IntegralSystemRealization.OpenComparisons l E system composition
  ringed : IntegralSystemRealization.RingedModels l E
  ringedOpens : IntegralSystemRealization.RingedOpenComparisons l E ringed
  realization : IntegralSystemRealization.RealizationModel l E system
  unitReduction : ∀ X : Scheme.{u},
    (IntegralSystemRealization.calculus l E X).reduction.obj
      (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit ≅
    (IntegralSystemRealization.calculus l E X).systemClosed.monoidal.tensorUnit
  unitNormalization : ∀ (X : Scheme.{u})
      (K : DerivedCategory (scalarReductionSource l E X)),
    (IntegralSystemRealization.calculus l E X).reductionTensor.inv.app
        ((IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit, K) ≫
      (IntegralSystemRealization.calculus l E X).reduction.map
        ((IntegralSystemRealization.calculus l E X).integralClosed.monoidal.leftUnitor K).hom =
    (IntegralSystemRealization.calculus l E X).systemClosed.tensor.map
      (Prod.mkHom (unitReduction X).hom (𝟙 _)) ≫
    ((IntegralSystemRealization.calculus l E X).systemClosed.monoidal.leftUnitor
      ((IntegralSystemRealization.calculus l E X).reduction.obj K)).hom

/-- The finite words in the source statement.
Source: blueprint coherence proof, steps 1--5
(blueprint: lem-sf-generator-reduction-coherence). -/
inductive Word {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S) :
    S → Type (max u s i) where
  | input (k : I) : Word W location (location k)
  | unit (a : S) : Word W location a
  | tensor {a : S} (B C : Word W location a) : Word W location a
  | pull {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (B : Word W location b) : Word W location a
  | push {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
      (B : Word W location a) : Word W location b
  | open {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) : Word W location b

/-- The corresponding structural recursion of the finite operation word.
Source: blueprint coherence proof, steps 2--5
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.length {a : S} : Word W location a → ℕ
  | .input _ | .unit _ => 0
  | .tensor B C => B.length + C.length + 1
  | .pull _ _ _ _ B | .push _ _ _ _ _ B | .open _ _ _ B => B.length + 1

/-- The listed structural generator kinds; no arbitrary pair of words is a generator.
Source: blueprint coherence proof, steps 1--5
(blueprint: lem-sf-generator-reduction-coherence). -/
inductive GeneratorKind : {a : S} → Word W location a → Word W location a → Type (max u s i) where
  | tensorAssociator {a : S} (B C D : Word W location a) :
      GeneratorKind (Word.tensor (Word.tensor B C) D) (Word.tensor B (Word.tensor C D))
  | tensorLeftUnit {a : S} (B : Word W location a) :
      GeneratorKind (Word.tensor (Word.unit a) B) B
  | tensorRightUnit {a : S} (B : Word W location a) :
      GeneratorKind (Word.tensor B (Word.unit a)) B
  | pullComposition {a b c : S} (f : W a ⟶ W b) (g : W b ⟶ W c)
      (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
      (hsg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
      (hs : IsSeparated (f ≫ g)) (ht : LocallyOfFiniteType (f ≫ g))
      (hq : QuasiCompact (f ≫ g)) (B : Word W location c) :
      GeneratorKind (Word.pull f hsf htf hqf (Word.pull g hsg htg hqg B))
        (Word.pull (f ≫ g) hs ht hq B)
  | pushComposition {a b c : S} (f : W a ⟶ W b) (g : W b ⟶ W c)
      (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
      (hpf : IsProper f) (hsg : IsSeparated g) (htg : LocallyOfFiniteType g)
      (hqg : QuasiCompact g) (hpg : IsProper g) (hs : IsSeparated (f ≫ g))
      (ht : LocallyOfFiniteType (f ≫ g)) (hq : QuasiCompact (f ≫ g))
      (hp : IsProper (f ≫ g)) (B : Word W location a) :
      GeneratorKind (Word.push g hsg htg hqg hpg (Word.push f hsf htf hqf hpf B))
        (Word.push (f ≫ g) hs ht hq hp B)
  | pullPushUnit {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
      (B : Word W location b) :
      GeneratorKind B (Word.push f hs ht hq hp (Word.pull f hs ht hq B))
  | pullPushCounit {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
      (B : Word W location a) :
      GeneratorKind (Word.pull f hs ht hq (Word.push f hs ht hq hp B)) B
  | openUnit {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) :
      GeneratorKind B (Word.pull j (by let := hj; infer_instance)
        (by let := hj; infer_instance) hq (Word.open j hj hq B))
  | openCounit {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location b) :
      GeneratorKind (Word.open j hj hq (Word.pull j
        (by let := hj; infer_instance) (by let := hj; infer_instance) hq B)) B
  | openBaseChange {a b c d : S}
      (gU : W a ⟶ W b) (j' : W a ⟶ W c) (j : W b ⟶ W d) (g : W c ⟶ W d)
      (h : gU ≫ j = j' ≫ g) (sq : IsPullback gU j' j g)
      (hgU : IsSeparated gU) (htgU : LocallyOfFiniteType gU) (hqgU : QuasiCompact gU)
      (hg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
      (hj' : IsOpenImmersion j') (hqj' : QuasiCompact j')
      (hj : IsOpenImmersion j) (hqj : QuasiCompact j) (B : Word W location b) :
      GeneratorKind
        (Word.pull g hg htg hqg (Word.open j hj hqj B))
        (Word.open j' hj' hqj' (Word.pull gU hgU htgU hqgU B))
  | openTensor {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) (C : Word W location b) :
      GeneratorKind (Word.tensor (Word.open j hj hq B) C)
        (Word.open j hj hq (Word.tensor B (Word.pull j (by let := hj; infer_instance)
          (by let := hj; infer_instance) hq C)))
  | properOpenInterchange {a b c d : S}
      (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (i : W c ⟶ W d)
      (h : k ≫ p = r ≫ i) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
      (hi : IsOpenImmersion i) (hii : QuasiCompact i)
      (hr : IsProper r) (hp : IsProper p) (B : Word W location a) :
      GeneratorKind
        (Word.open i hi hii (Word.push r (by let := hr; infer_instance)
          (by let := hr; infer_instance) (by let := hr; infer_instance) hr B))
        (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
          (by let := hp; infer_instance) hp (Word.open k hk hki B))
  | properOpenLambda {a b c d : S}
      (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (i : W c ⟶ W d)
      (h : k ≫ p = r ≫ i) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
      (hi : IsOpenImmersion i) (hii : QuasiCompact i)
      (hr : IsProper r) (hp : IsProper p) (B : Word W location a) :
      GeneratorKind
        (Word.pull i (by let := hi; infer_instance) (by let := hi; infer_instance) hii
          (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
            (by let := hp; infer_instance) hp (Word.open k hk hki B)))
        (Word.push r (by let := hr; infer_instance) (by let := hr; infer_instance)
          (by let := hr; infer_instance) hr B)

/-- The system interpretation uses the actual derived adjunctions and tensor.
Source: blueprint coherence proof, step 1
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.systemValue (o : Operations l E)
    (M : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    {a : S} → Word W location a → coefficientSequenceDerived l E (W a)
  | _, .input k => M k
  | a, .unit _ => (IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.tensorUnit
  | a, .tensor B C => (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.obj
      (B.systemValue o M, C.systemValue o M)
  | _, .pull f _ _ _ B => (IntegralSystemRealization.pull l E f).obj (B.systemValue o M)
  | _, .push f _ _ _ _ B =>
      (IntegralSystemRealization.Operations.push l E o.system f).obj (B.systemValue o M)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.Operations.shriek l E o.system j).obj (B.systemValue o M)

/-- The ordinary integral ringed-site interpretation, before quotient completion.
Source: blueprint coherence proof, steps 3--4
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.ringedValue (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → Word W location a → DerivedCategory (scalarReductionSource l E (W a))
  | _, .input k => K k
  | a, .unit _ => (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit
  | a, .tensor B C => (o.ringed.tensor (W a)).ordinary.tensor.obj
      (B.ringedValue o K, C.ringedValue o K)
  | _, .pull f _ _ _ B =>
      (IntegralSystemRealization.ringedPull l E f).obj (B.ringedValue o K)
  | _, .push f _ _ _ _ B =>
      (IntegralSystemRealization.ringedPush l E f).obj (B.ringedValue o K)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).obj (B.ringedValue o K)

/-- Select the actual system arrow by recursion on the structural generator.
The proper/open case is the open adjunct of inverse lambda; lambda itself is the
published cartesian-conjugation/clopen/compositor composite. No arrow is supplied
by the generator's caller.
Source: blueprint coherence proof, steps 3--4
(blueprint: lem-sf-generator-reduction-coherence). -/
def GeneratorKind.systemMap (o : Operations l E)
    (M : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    {a : S} → {B C : Word W location a} → GeneratorKind W location B C →
      (B.systemValue l E W location o M ⟶ C.systemValue l E W location o M)
  | a, _, _, .tensorAssociator B C D =>
      ((IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.associator
        (B.systemValue l E W location o M) (C.systemValue l E W location o M)
        (D.systemValue l E W location o M)).hom
  | a, _, _, .tensorLeftUnit B =>
      ((IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.leftUnitor
        (B.systemValue l E W location o M)).hom
  | a, _, _, .tensorRightUnit B =>
      ((IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal.rightUnitor
        (B.systemValue l E W location o M)).hom
  | _, _, _, .pullComposition f g _ _ _ _ _ _ _ _ _ B =>
      (o.composition.pullComp f g).inv.app (B.systemValue l E W location o M)
  | _, _, _, .pushComposition f g _ _ _ _ _ _ _ _ _ _ _ _ B =>
      (o.composition.pushComp l E f g).hom.app (B.systemValue l E W location o M)
  | _, _, _, .pullPushUnit f _ _ _ _ B =>
      (o.system.direct f).adj.unit.app (B.systemValue l E W location o M)
  | _, _, _, .pullPushCounit f _ _ _ _ B =>
      (o.system.direct f).adj.counit.app (B.systemValue l E W location o M)
  | _, _, _, .openUnit j hj _ B => letI := hj
      (o.system.extension j).adj.unit.app (B.systemValue l E W location o M)
  | _, _, _, .openCounit j hj _ B => letI := hj
      (o.system.extension j).adj.counit.app (B.systemValue l E W location o M)
  | _, _, _, .openBaseChange v j' j g h sq _ _ _ _ _ _ hj' _ hj _ B =>
      letI := hj'; letI := hj
      (o.opens.beta v j' j g h sq).hom.app (B.systemValue l E W location o M)
  | _, _, _, .openTensor j hj _ B C => letI := hj
      (o.opens.projection j).hom.app
        (B.systemValue l E W location o M, C.systemValue l E W location o M)
  | _, _, _, .properOpenInterchange k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      ((o.system.extension j).adj.homEquiv _ _).symm
        ((IntegralSystemRealization.properOpenLambda l E o.system o.composition o.opens
          k r p j h).inv.app (B.systemValue l E W location o M))
  | _, _, _, .properOpenLambda k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      (IntegralSystemRealization.properOpenLambda l E o.system o.composition o.opens
        k r p j h).hom.app (B.systemValue l E W location o M)

/-- Select the independently defined ordinary ringed-site generator. In particular,
its units and counits are the actual geometric/open adjunction transformations;
the proper/open map uses the ringed clopen factorization, independently of system
reduction or any realization square.
Source: blueprint coherence proof, steps 3--4
(blueprint: lem-sf-generator-reduction-coherence). -/
def GeneratorKind.ringedMap (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → {B C : Word W location a} → GeneratorKind W location B C →
      (B.ringedValue l E W location o K ⟶ C.ringedValue l E W location o K)
  | a, _, _, .tensorAssociator B C D =>
      (IntegralSystemRealization.ringedAssociator l E o.ringed (W a)
        (B.ringedValue l E W location o K) (C.ringedValue l E W location o K)
        (D.ringedValue l E W location o K)).hom
  | a, _, _, .tensorLeftUnit B =>
      (eqToIso (congrArg (fun T : DerivedCategory (scalarReductionSource l E (W a)) ×
        DerivedCategory (scalarReductionSource l E (W a)) ⥤
        DerivedCategory (scalarReductionSource l E (W a)) ↦
          T.obj ((IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit,
            B.ringedValue l E W location o K)) (o.ringed.tensorClosed (W a)))).hom ≫
      ((IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.leftUnitor
        (B.ringedValue l E W location o K)).hom
  | a, _, _, .tensorRightUnit B =>
      (eqToIso (congrArg (fun T : DerivedCategory (scalarReductionSource l E (W a)) ×
        DerivedCategory (scalarReductionSource l E (W a)) ⥤
        DerivedCategory (scalarReductionSource l E (W a)) ↦
          T.obj (B.ringedValue l E W location o K,
            (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit))
          (o.ringed.tensorClosed (W a)))).hom ≫
      ((IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.rightUnitor
        (B.ringedValue l E W location o K)).hom
  | _, _, _, .pullComposition f g _ _ _ _ _ _ _ _ _ B =>
      (IntegralSystemRealization.ringedPullComp l E f g).inv.app
        (B.ringedValue l E W location o K)
  | _, _, _, .pushComposition f g _ _ _ _ _ _ _ _ _ _ _ _ B =>
      (IntegralSystemRealization.ringedPushComp l E f g).hom.app
        (B.ringedValue l E W location o K)
  | _, _, _, .pullPushUnit f _ _ _ _ B =>
      (IntegralSystemRealization.ringedAdj l E f).unit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .pullPushCounit f _ _ _ _ B =>
      (IntegralSystemRealization.ringedAdj l E f).counit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .openUnit j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpenAdj l E j).unit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .openCounit j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpenAdj l E j).counit.app
        (B.ringedValue l E W location o K)
  | _, _, _, .openBaseChange v j' j g h sq _ _ _ _ _ _ hj' _ hj _ B =>
      letI := hj'; letI := hj
      (o.ringedOpens.beta v j' j g h sq).hom.app (B.ringedValue l E W location o K)
  | _, _, _, .openTensor j hj _ B C => letI := hj
      (o.ringedOpens.projection j).hom.app
        (B.ringedValue l E W location o K, C.ringedValue l E W location o K)
  | _, _, _, .properOpenInterchange k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      ((IntegralSystemRealization.ringedOpenAdj l E j).homEquiv _ _).symm
        ((IntegralSystemRealization.ringedProperOpenLambda l E o.ringed o.ringedOpens
          k r p j h).inv.app (B.ringedValue l E W location o K))
  | _, _, _, .properOpenLambda k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      (IntegralSystemRealization.ringedProperOpenLambda l E o.ringed o.ringedOpens
        k r p j h).hom.app (B.ringedValue l E W location o K)

/-- Invert an actual comparison where invertible; the value elsewhere is irrelevant
on the theorem's domain. Source: blueprint coherence proof, complete restriction
(blueprint: lem-sf-generator-reduction-coherence). -/
def inverseOrZero {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) : Y ⟶ X := by
  classical
  exact if h : IsIso f then @inv C _ X Y f h else 0

/-- The integral proper image is its strict system direct-image tower followed by
actual total limit. The system image is the recorded derived right adjoint.
Source: blueprint coherence proof, step 2
(blueprint: lem-sf-generator-reduction-coherence). -/
def integralPush (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  integralSystemDerivedDirectImage l E o.system f

/-- Canonical ordinary-to-completed tensor map, from the real completion unit.
Source: blueprint coherence proof, step 3
(blueprint: lem-sf-generator-reduction-coherence). -/
def tensorCompletion (o : Operations l E) (X : Scheme.{u}) :=
  (o.ringed.tensor X).chi l E

/-- The coefficient map of completed tensor uses the ordinary tensor reduction and
inverse reduction of the actual completion unit. It is independent of d_tensor.
Source: blueprint coherence proof, step 2
(blueprint: lem-sf-generator-reduction-coherence). -/
def tensorR (o : Operations l E) (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource l E X)) :=
  inverseOrZero ((IntegralSystemRealization.calculus l E X).reduction.map
    ((tensorCompletion l E o X).app (K, L))) ≫
  (IntegralSystemRealization.calculus l E X).reduction.map
    ((eqToIso (congrArg (fun T : DerivedCategory (scalarReductionSource l E X) ×
      DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E X) ↦ T.obj (K, L))
      (o.ringed.tensorClosed X))).hom) ≫
  (IntegralSystemRealization.calculus l E X).reductionTensor.hom.app (K, L)

/-- Canonical coefficient map of completed pullback, obtained from the fixed
whole-system pullback comparison and reduction of the quotient-completion unit.
Source: blueprint coherence proof, step 2
(blueprint: lem-sf-generator-reduction-coherence). -/
def pullR (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E Y)) :=
  inverseOrZero ((IntegralSystemRealization.calculus l E X).reduction.map
    (((o.ringed.pull f).unit l E).app K)) ≫
  (o.realization.reductionPull f).hom.app K

/-- The actual counit is the coefficient comparison of the defining proper tower.
Source: blueprint coherence proof, step 2
(blueprint: lem-sf-generator-reduction-coherence). -/
def pushR (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :=
  (IntegralSystemRealization.calculus l E Y).adjunction.counit.app
    ((IntegralSystemRealization.Operations.push l E o.system f).obj
      ((IntegralSystemRealization.calculus l E X).reduction.obj K))

/-- The specified open coefficient comparison, transported from the recorded
localized open interface to the same actual functors used by the generators.
Source: blueprint coherence proof, step 2; Stacks 03DI and 07A7
(blueprint: lem-sf-generator-reduction-coherence). -/
def openR (o : Operations l E) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X)) :=
  inverseOrZero ((o.realization.openReduction l E j).app K)

/-- The specified open realization, from the actual mate and reconstruction unit.
It is a map on the ambient category; its inverse laws are asserted on complete inputs.
Source: Stacks 03DI, 07A7; blueprint coherence proof, step 2
(blueprint: lem-sf-generator-reduction-coherence). -/
def openD (o : Operations l E) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X)) :=
  (coefficientSequenceLimit l E Y).map ((o.realization.openReduction l E j).app K) ≫
    inverseOrZero ((IntegralSystemRealization.calculus l E Y).adjunction.unit.app
      ((IntegralSystemRealization.ringedOpen l E j).obj K))

/-- Integral evaluation uses the prescribed completed tensor/pullback, the proper
strict tower, and the localized ringed open extension.
Source: blueprint coherence proof, steps 2--5
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.integralValue (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → Word W location a → DerivedCategory (scalarReductionSource l E (W a))
  | _, .input k => K k
  | a, .unit _ => (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit
  | a, .tensor B C => (integralCompletedTensor l E (W a)).obj
      (B.integralValue o K, C.integralValue o K)
  | _, .pull f _ _ _ B => (integralDerivedPullback l E f).obj (B.integralValue o K)
  | _, .push f _ _ _ _ B => (integralPush l E o f).obj (B.integralValue o K)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).obj (B.integralValue o K)

/-- Quotient completion applied recursively to ordinary ringed expressions.
The proper step is the ordinary direct-image/limit comparison and the actual
reconstruction unit. It is defined before any coefficient square.
Source: blueprint coherence proof, steps 2--4
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.completionMap (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      B.ringedValue l E W location o K ⟶ B.integralValue l E W location o K
  | _, .input _ | _, .unit _ => 𝟙 _
  | a, .tensor B C => (o.ringed.tensor (W a)).ordinary.tensor.map
      (Prod.mkHom (B.completionMap o K) (C.completionMap o K)) ≫
      (tensorCompletion l E o (W a)).app
        (B.integralValue l E W location o K, C.integralValue l E W location o K)
  | _, .pull f _ _ _ B =>
      (IntegralSystemRealization.ringedPull l E f).map (B.completionMap o K) ≫
      ((o.ringed.pull f).unit l E).app (B.integralValue l E W location o K)
  | _, .push f _ _ _ _ B =>
      (IntegralSystemRealization.ringedPush l E f).map (B.completionMap o K) ≫
      (IntegralSystemRealization.ringedPush l E f).map
        ((IntegralSystemRealization.calculus l E _).adjunction.unit.app
          (B.integralValue l E W location o K)) ≫
      (o.realization.push l E f).inv.app
        ((IntegralSystemRealization.calculus l E _).reduction.obj
          (B.integralValue l E W location o K))
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).map (B.completionMap o K)

/-- The canonical completed ringed-site generator: transport the separately
constructed ringed generator along the actual recursive completion maps.
Neither coefficient reduction nor r_B nor the desired square defines this map.
Source: blueprint coherence proof, steps 3--4
(blueprint: lem-sf-generator-reduction-coherence). -/
def GeneratorKind.integralMap (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) :=
  inverseOrZero (B.completionMap l E W location o K) ≫
    g.ringedMap l E W location o K ≫ C.completionMap l E W location o K

/-- Reduce the input family in the actual whole-system calculus.
Source: blueprint coherence proof, step 1
(blueprint: lem-sf-generator-reduction-coherence). -/
def inputReduction
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (k : I) := (IntegralSystemRealization.calculus l E (W (location k))).reduction.obj (K k)

/-- Successive actual primitive coefficient comparisons, with both tensor slots
and every inner operation applied functorially.
Source: blueprint coherence proof, steps 2--5
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.r (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      (IntegralSystemRealization.calculus l E (W a)).reduction.obj
        (B.integralValue l E W location o K) ⟶
      B.systemValue l E W location o (inputReduction l E W location K)
  | _, .input _ => 𝟙 _
  | a, .unit _ => (o.unitReduction (W a)).hom
  | a, .tensor B C => tensorR l E o (W a)
      (B.integralValue l E W location o K) (C.integralValue l E W location o K) ≫
      (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
        (Prod.mkHom (B.r o K) (C.r o K))
  | _, .pull f _ _ _ B => pullR l E o f (B.integralValue l E W location o K) ≫
      (IntegralSystemRealization.pull l E f).map (B.r o K)
  | _, .push f _ _ _ _ B => pushR l E o f (B.integralValue l E W location o K) ≫
      (IntegralSystemRealization.Operations.push l E o.system f).map (B.r o K)
  | _, .open j hj _ B => letI := hj
      openR l E o j (B.integralValue l E W location o K) ≫
      (IntegralSystemRealization.Operations.shriek l E o.system j).map (B.r o K)

/-- The actual normalized system domain with the specified common intervals.
The witness is the recorded `Origins`, whose levels use `FixedEtaleOriginWitness`.
Source: blueprint coherence proof, step 1
(blueprint: lem-sf-generator-reduction-coherence). -/
def SystemAdmissible (X : Scheme.{u}) (M : coefficientSequenceDerived l E X)
    (lo hi torLo torHi : ℤ) : Prop :=
  IsNormalizedCoefficientSequence l E X M ∧
  Nonempty (IntegralSystemRealization.Origins l E X M) ∧
  lo ≤ hi ∧ torLo ≤ torHi ∧ ∀ n : ℕ,
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) ∧
    proEtaleCohomologicalSupport
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) ⊆ Set.Icc lo hi ∧
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) torLo torHi

/-- The derived-complete constructible finite-Tor input and its actual reduction system.
Source: blueprint coherence proof, step 1
(blueprint: lem-sf-generator-reduction-coherence). -/
def Admissible {X : Scheme.{u}} (Syst : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) (lo hi torLo torHi : ℤ) : Prop :=
  finiteTorConstructibleIntegral l E X K ∧
  SystemAdmissible l E X (Syst.reduction.obj K) lo hi torLo torHi

/-- Restrict precisely the actual systems at the vertices of this word, recursively
in each tensor slot; no condition is imposed on unrelated words.
Source: blueprint coherence proof, steps 1 and 4
(blueprint: lem-sf-generator-reduction-coherence). -/
def Word.admissible {a : S} (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ) (B : Word W location a) : Prop :=
  SystemAdmissible l E (W a)
    (Word.systemValue l E W location o (inputReduction l E W location K) B) lo hi torLo torHi ∧
    match B with
    | .input _ | .unit _ => True
    | .tensor C D => C.admissible o K lo hi torLo torHi ∧
        D.admissible o K lo hi torLo torHi
    | .pull _ _ _ _ C | .push _ _ _ _ _ C | .open _ _ _ C =>
        C.admissible o K lo hi torLo torHi

/-- Common bounds at every object in the cartesian/clopen factorization of lambda.
This includes the internal systems on V ×_Z W, independently of the length bound
on the two generator endpoints. Source: blueprint proof, step 4
(blueprint: lem-sf-generator-reduction-coherence). -/
def lambdaAdmissible (o : Operations l E) {U V T Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ T) (p : V ⟶ Z) (j : T ⟶ Z)
    [IsOpenImmersion k] [QuasiCompact k] [IsOpenImmersion j] [QuasiCompact j]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ j)
    (M : coefficientSequenceDerived l E U) (lo hi torLo torHi : ℤ) : Prop :=
  SystemAdmissible l E (pullback p j)
    ((IntegralSystemRealization.pull l E (pullback.fst p j)).obj
      ((IntegralSystemRealization.Operations.shriek l E o.system k).obj M))
    lo hi torLo torHi ∧
  SystemAdmissible l E (pullback p j)
    ((IntegralSystemRealization.Operations.shriek l E o.system
      (ProEtale.StrictTower.squareLift k r p j h)).obj M) lo hi torLo torHi ∧
  SystemAdmissible l E (pullback p j)
    ((IntegralSystemRealization.Operations.push l E o.system
      (ProEtale.StrictTower.squareLift k r p j h)).obj M) lo hi torLo torHi ∧
  SystemAdmissible l E T
    ((IntegralSystemRealization.Operations.push l E o.system (pullback.snd p j)).obj
      ((IntegralSystemRealization.pull l E (pullback.fst p j)).obj
        ((IntegralSystemRealization.Operations.shriek l E o.system k).obj M)))
    lo hi torLo torHi ∧
  SystemAdmissible l E T
    ((IntegralSystemRealization.Operations.push l E o.system (pullback.snd p j)).obj
      ((IntegralSystemRealization.Operations.shriek l E o.system
        (ProEtale.StrictTower.squareLift k r p j h)).obj M)) lo hi torLo torHi ∧
  SystemAdmissible l E T
    ((IntegralSystemRealization.Operations.push l E o.system (pullback.snd p j)).obj
      ((IntegralSystemRealization.Operations.push l E o.system
        (ProEtale.StrictTower.squareLift k r p j h)).obj M)) lo hi torLo torHi

/-- Restriction to the actual additional systems used by a generator.
Source: blueprint coherence proof, steps 1 and 4
(blueprint: lem-sf-generator-reduction-coherence). -/
def GeneratorKind.admissible (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ) :
    {a : S} → {B C : Word W location a} → GeneratorKind W location B C → Prop
  | _, _, _, .properOpenInterchange k r p j h hk qk hj qj hr hp B
  | _, _, _, .properOpenLambda k r p j h hk qk hj qj hr hp B =>
      letI := hk; letI := qk; letI := hj; letI := qj; letI := hr; letI := hp
      lambdaAdmissible l E o k r p j h
        (B.systemValue l E W location o (inputReduction l E W location K)) lo hi torLo torHi
  | _, _, _, _ => True

/-- The actual coefficient square, as a proposition about two specified maps.
Source: blueprint coherence proof, step 5
(blueprint: lem-sf-generator-reduction-coherence). -/
def Assertion (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  B.r l E W location o K ≫
    g.systemMap l E W location o (inputReduction l E W location K) =
  (IntegralSystemRealization.calculus l E (W a)).reduction.map
    (g.integralMap l E W location o K) ≫ C.r l E W location o K

/-- Finite-type structures over the fixed algebraic closure. Source: blueprint
coherence proof, step 1 (blueprint: lem-sf-generator-reduction-coherence). -/
structure FiniteTypeFamily (k : Type u) [CommRing k] where
  structureMap : ∀ a : S, W a ⟶ Spec (CommRingCat.of k)
  locallyFiniteType : ∀ a : S, LocallyOfFiniteType (structureMap a)
  quasiCompact : ∀ a : S, QuasiCompact (structureMap a)

end WeilConjectures.GeneratorReduction
