/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import WeilConjectures.SecSmoothPurity.CochainCompositeHom
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData

/-! # Balanced coefficient comparisons on sheaves of modules

Source: Stacks Project, Modules on Sites, Section 03EK and Tag 03EL,
lemma-tensor-product-pullback.
(auxiliary; not a blueprint node).

All tensor sections below are sections of the actual sheafified tensor. The transported
insertion is a morphism on the algebraic inverse image, so its argument is an arbitrary
local section there. No lifting of local sections to the source site is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [local irreducible] SheafOfModules.monoidalCategory

universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback
open SheafOfModules

namespace CategoryTheory.CoefficientComparisonsBalanced

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The coefficient square and its algebraic inverse-image presentations. The graph equation
specifies that j is the inverse image of iY under the given identifications.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
structure Square (F : Sheaf J (Type w) ⥤ Sheaf K (Type w)) where
  R0 : Sheaf J CommRingCat.{w}
  R1 : Sheaf J CommRingCat.{w}
  B0 : Sheaf K CommRingCat.{w}
  B1 : Sheaf K CommRingCat.{w}
  A0 : Sheaf K CommRingCat.{w}
  A1 : Sheaf K CommRingCat.{w}
  iY : R0 ⟶ R1
  iX : B0 ⟶ B1
  j : A0 ⟶ A1
  phi0 : A0 ⟶ B0
  phi1 : A1 ⟶ B1
  I0 : AlgebraicInverseImage F R0 A0
  I1 : AlgebraicInverseImage F R1 A1
  graph : F.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map iY) ≫
      I1.ringUnderlying.hom = I0.ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map j
  commutes : phi0 ≫ iX = j ≫ phi1

variable {F : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (d : Square F)

/-- F_0 is the specified algebraic inverse image followed by sheafified scalar extension.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def pull0 : Modules.{w, uC, vC} d.R0 ⥤ Modules.{w, uD, vD} d.B0 :=
  d.I0.modules ⋙ extensionFunctor.{w, uD, vD} d.phi0

/-- F_1 is the specified algebraic inverse image followed by sheafified scalar extension.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def pull1 : Modules.{w, uC, vC} d.R1 ⥤ Modules.{w, uD, vD} d.B1 :=
  d.I1.modules ⋙ extensionFunctor.{w, uD, vD} d.phi1

/-- The source S_X F_0 of k, in diagrammatic functor-composition order.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def left : Modules.{w, uC, vC} d.R0 ⥤ Modules.{w, uD, vD} d.B1 :=
  pull0 d ⋙ extensionFunctor.{w, uD, vD} d.iX

/-- The target F_1 S_Y of k, in diagrammatic functor-composition order.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def right : Modules.{w, uC, vC} d.R0 ⥤ Modules.{w, uD, vD} d.B1 :=
  extensionFunctor.{w, uC, vC} d.iY ⋙ pull1 d

/-- The single pullback with coefficient map i_X phi^0 = phi^1 u^{-1}i_Y.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def common : Modules.{w, uC, vC} d.R0 ⥤ Modules.{w, uD, vD} d.B1 :=
  d.I0.modules ⋙ extensionFunctor.{w, uD, vD} (d.phi0 ≫ d.iX)

/-- The inverse image of x mapped to 1 tensor x. This is defined on the entire underlying
inverse-image sheaf, not merely on inverse images of source-site local sections.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def transportedInsertion (M : Modules.{w, uC, vC} d.R0) :
    (underlying d.A0).obj (d.I0.modules.obj M) ⟶
      (underlying d.A1).obj (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) :=
  d.I0.moduleUnderlying.hom.app M ≫ F.map (insertion d.iY M) ≫
    d.I1.moduleUnderlying.inv.app ((extensionFunctor.{w, uC, vC} d.iY).obj M)

/-- The two generator formulas for k and its inverse. The expression d • transportedInsertion x
is the algebraic inverse image of d tensor x in S_Y M; its d and x are arbitrary local
sections of the inverse-image ring and module.
Source: Stacks 03EK, 03EL
(auxiliary; not a blueprint node). -/
def PullbackFormulas (k : left d ≅ right d) : Prop :=
  (∀ (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (b : d.B1.obj.obj U) (a : d.B0.obj.obj U)
      (x : (d.I0.modules.obj M).val.obj U),
    (k.hom.app M).val.app U
      (extensionTmul d.iX ((pull0 d).obj M) U b
        (extensionTmul d.phi0 (d.I0.modules.obj M) U a x)) =
      extensionTmul d.phi1 (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) U
        (b * d.iX.hom.app U a) ((transportedInsertion d M).hom.app U x)) ∧
  (∀ (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (b : d.B1.obj.obj U) (a : d.A1.obj.obj U)
      (x : (d.I0.modules.obj M).val.obj U),
    (k.inv.app M).val.app U
      (extensionTmul d.phi1 (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) U b
        (a • (@id ((d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)).val.obj U)
          ((transportedInsertion d M).hom.app U x)))) =
      extensionTmul d.iX ((pull0 d).obj M) U (b * d.phi1.hom.app U a)
        (extensionTmul d.phi0 (d.I0.modules.obj M) U 1 x))

/-- Identification with the two normalized comparisons from the single pullback.
Both comparisons are natural isomorphisms, fixed on all scalar-extension generators.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def ViaCommonPullback (k : left d ≅ right d) : Prop :=
  ∃ (l : common d ≅ left d) (h : common d ≅ right d),
    (∀ (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (b : d.B1.obj.obj U)
        (x : (d.I0.modules.obj M).val.obj U),
      (l.hom.app M).val.app U
        (extensionTmul (d.phi0 ≫ d.iX) (d.I0.modules.obj M) U b x) =
        extensionTmul d.iX ((pull0 d).obj M) U b
          (extensionTmul d.phi0 (d.I0.modules.obj M) U 1 x)) ∧
    (∀ (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (b : d.B1.obj.obj U)
        (x : (d.I0.modules.obj M).val.obj U),
      (h.hom.app M).val.app U
        (extensionTmul (d.phi0 ≫ d.iX) (d.I0.modules.obj M) U b x) =
        extensionTmul d.phi1 (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) U b
          ((transportedInsertion d M).hom.app U x)) ∧
    k = l.symm ≪≫ h

/-- Forward and inverse scalar/tensor prescriptions, on the actual sheafified tensor.
Source: Stacks 03EK, 03EL
(auxiliary; not a blueprint node). -/
def ScalarTensorFormulas {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (s : RingedComparisonTensor A B (extensionFunctor.{w, uC, vC} i)) : Prop :=
  (∀ (M N : Modules.{w, uC, vC} A) (U : Cᵒᵖ) (b : B.obj.obj U)
      (x : M.val.obj U) (y : N.val.obj U),
    (s M N).hom.val.app U
      (extensionTmul i ((monoidalCategory A).tensorObj M N) U b
        (ringedComparisonPure A M N U x y)) =
      ringedComparisonPure B ((extensionFunctor.{w, uC, vC} i).obj M)
        ((extensionFunctor.{w, uC, vC} i).obj N) U
        (extensionTmul i M U b x) (extensionTmul i N U 1 y)) ∧
  (∀ (M N : Modules.{w, uC, vC} A) (U : Cᵒᵖ) (b c : B.obj.obj U)
      (x : M.val.obj U) (y : N.val.obj U),
    (s M N).inv.val.app U
      (ringedComparisonPure B ((extensionFunctor.{w, uC, vC} i).obj M)
        ((extensionFunctor.{w, uC, vC} i).obj N) U
        (extensionTmul i M U b x) (extensionTmul i N U c y)) =
      extensionTmul i ((monoidalCategory A).tensorObj M N) U (b * c)
        (ringedComparisonPure A M N U x y))

/-- The scalar comparison existence and uniqueness assertion, including its identification
with every canonical normalized comparison for the identity geometric morphism.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def ScalarTensorConstruction {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B) : Prop :=
  ∃! s : RingedComparisonTensor A B (extensionFunctor.{w, uC, vC} i),
    ScalarTensorFormulas i s ∧
      ringedComparisonNaturality A B (extensionFunctor.{w, uC, vC} i) s ∧
    ∀ c : CanonicalRingedTensorComparisonOnSmallSites A B A (𝟭 _)
      (identityAlgebraicInverseImage A) i (extensionFunctor.{w, uC, vC} i)
        (fun _ ↦ rfl), c.mu = s

/-- Forgetting commutativity preserves sheaves. Cache the existing Mathlib instance locally
so that coefficient-comparison types do not repeat its multicospan inference.
Source: Mathlib, Sites.Whiskering, `hasSheafCompose_of_preservesMulticospan`.
(auxiliary; not a blueprint node).
Proof: apply Mathlib's instance for the limit-preserving forgetful functor. -/
private theorem coefficientComparison_hasSheafCompose
    {E : Type uC} [Category.{vC} E] [EssentiallySmall.{w} E]
    (T : GrothendieckTopology E) :
    T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

attribute [local instance 2000] coefficientComparison_hasSheafCompose

open scoped ChangeOfRings TensorProduct
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] tensorObjIsoSheafification
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  PresheafOfModules.sheafification

section Proof

variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

private theorem extension_smul {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (M : Modules.{w, uC, vC} A) (U : Cᵒᵖ) (b c : B.obj.obj U) (x : M.val.obj U) :
    extensionTmul i M U (b * c) x = b • extensionTmul i M U c x := by
  unfold extensionTmul
  exact (((PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B).obj)).unit.app
      (changeOfRingsPresheaf.{vC, uC, w} i M)).app U).hom.map_smul b
        (c ⊗ₜ[A.obj.obj U, (i.hom.app U).hom] x)

private theorem extension_scalar {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (M : Modules.{w, uC, vC} A) (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    extensionTmul i M U b x = b • extensionTmul i M U 1 x :=
  (congrArg (fun z ↦ extensionTmul i M U z x) (mul_one b)).symm.trans
    (extension_smul i M U b 1 x)

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem extension_balance {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (M : Modules.{w, uC, vC} A) (U : Cᵒᵖ) (b : B.obj.obj U) (a : A.obj.obj U)
    (x : M.val.obj U) :
    extensionTmul i M U b (a • x) = extensionTmul i M U (b * i.hom.app U a) x := by
  unfold extensionTmul
  congr 1
  let := (i.hom.app U).hom.toAlgebra
  change b ⊗ₜ[A.obj.obj U] (a • x) =
    (b * i.hom.app U a) ⊗ₜ[A.obj.obj U] x
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact congrArg (fun z : B.obj.obj U ↦
    z ⊗ₜ[A.obj.obj U, (i.hom.app U).hom] x) (mul_comm (i.hom.app U a) b)

private theorem extension_unit_ext {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (M : Modules.{w, uC, vC} A) (H : Modules.{w, uC, vC} B)
    {f g : (extensionFunctor.{w, uC, vC} i).obj M ⟶ H}
    (h : ∀ U x, f.val.app U (extensionTmul i M U 1 x) =
      g.val.app U (extensionTmul i M U 1 x)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B).obj)
  apply (adj.homEquiv (changeOfRingsPresheaf.{vC, uC, w} i M) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U x

private theorem pure_smul {A : Sheaf J CommRingCat.{w}} (M N : Modules.{w, uC, vC} A)
    (U : Cᵒᵖ) (a : A.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    (ringedComparisonPure A M N U (a • (@id (M.val.obj U) x)) y =
      a • ringedComparisonPure A M N U x y) ∧
    (ringedComparisonPure A M N U x (a • (@id (N.val.obj U) y)) =
      a • ringedComparisonPure A M N U x y) := by
  let f : M.val.obj U ⊗[A.obj.obj U] N.val.obj U →ₗ[A.obj.obj U]
      ((monoidalCategory A).tensorObj M N).val.obj U :=
    ((tensorObjIsoSheafification M N).inv.val.app U).hom.comp
      (((PresheafOfModules.sheafificationAdjunction.{w}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)).unit.app
          (M.val ⊗ N.val)).app U).hom
  exact ⟨(congrArg f (TensorProduct.smul_tmul' a x y).symm).trans (f.map_smul a _),
    (congrArg f (TensorProduct.tmul_smul a x y)).trans (f.map_smul a _)⟩

omit [EssentiallySmall.{w} C] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem iso_hom_inv_apply {A : Sheaf J CommRingCat.{w}}
    {M N : Modules.{w, uC, vC} A} (e : M ≅ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x :=
  congrArg (fun f : M ⟶ M ↦ f.val.app U x) e.hom_inv_id

attribute [local irreducible] extensionTmul ringedComparisonPure

private theorem scalar_linear_formulas {R : Type*} [Semiring R]
    {V W X Y : Type*}
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    {M N P : Type*} (f : V →ₗ[R] Y) (g : Y →ₗ[R] V)
    (hg : ∀ z, g (f z) = z)
    (η : R → P → V) (ηM : R → M → W) (ηN : R → N → X)
    (p : M → N → P) (q : W → X → Y)
    (hη : ∀ (b : R) (z : P), η b z = b • η 1 z)
    (hM : ∀ (b : R) (x : M), ηM b x = b • ηM 1 x)
    (hN : ∀ (b : R) (y : N), ηN b y = b • ηN 1 y)
    (hl : ∀ (b : R) (x : W) (y : X), q (b • x) y = b • q x y)
    (hr : ∀ (b : R) (x : W) (y : X), q x (b • y) = b • q x y)
    (hu : ∀ x y, f (η 1 (p x y)) = q (ηM 1 x) (ηN 1 y)) :
    (∀ b x y, f (η b (p x y)) = q (ηM b x) (ηN 1 y)) ∧
      (∀ b c x y, g (q (ηM b x) (ηN c y)) = η (b * c) (p x y)) := by
  constructor
  · intro b x y
    rw [hη, f.map_smul, hu, ← hl, ← hM]
  · intro b c x y
    have hi : g (q (ηM 1 x) (ηN 1 y)) = η 1 (p x y) := by
      rw [← hu]
      exact hg _
    rw [hM, hN, hl, hr, g.map_smul, g.map_smul, hi, smul_smul, ← hη]

attribute [local semireducible] extensionTmul
attribute [local semireducible] ringedComparisonPure
attribute [local irreducible] extensionComparison

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem insertion_section {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (M : Modules.{w, uC, vC} A) (U : Cᵒᵖ) (x : M.val.obj U) :
    (insertion i M).hom.app U x = extensionTmul i M U 1 x :=
  (Classical.choose_spec (extensionAdjunction_existsUnique i)).1 M U x

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem canonical_small
    (R : Sheaf J CommRingCat.{w}) (S RI : Sheaf K CommRingCat.{w})
    (L : Modules.{w, uC, vC} R ⥤ Modules.{w, uD, vD} S)
    (I : AlgebraicInverseImage F R RI) (c : RI ⟶ S)
    (ho : ∀ M, L.obj M = changeOfRings c (I.modules.obj M))
    (G : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : F ⊣ G)
    [PreservesFiniteLimits F]
    (hm : ∀ {M N} (f : M ⟶ N), L.map f = eqToHom (ho M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (ho N).symm) :
    Nonempty (CanonicalRingedTensorComparisonOnSmallSites R S RI F I c L ho) ∧
      Subsingleton (CanonicalRingedTensorComparisonOnSmallSites R S RI F I c L ho) := by
  obtain ⟨⟨a⟩, ha⟩ :=
    CochainTensorComparison.canonicalRingedTensorComparison_existsUnique R S RI F I c L ho
      G adj hm
  let f : CochainTensorComparison.CanonicalRingedTensorComparison R S RI F I c L ho →
      CanonicalRingedTensorComparisonOnSmallSites R S RI F I c L ho :=
    fun z ↦ ⟨z.q, z.q_one, z.mu, z.naturality, z.pure⟩
  let g : CanonicalRingedTensorComparisonOnSmallSites R S RI F I c L ho →
      CochainTensorComparison.CanonicalRingedTensorComparison R S RI F I c L ho :=
    fun z ↦ ⟨z.q, z.q_one, z.mu, z.naturality, z.pure⟩
  have hfg (z : CanonicalRingedTensorComparisonOnSmallSites R S RI F I c L ho) :
      f (g z) = z := by
    cases z
    rfl
  refine ⟨⟨f a⟩, ⟨fun b c ↦ ?_⟩⟩
  exact (hfg b).symm.trans ((congrArg f (ha.elim (g b) (g c))).trans (hfg c))

private theorem scalar_construction {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B) :
    ScalarTensorConstruction.{w, uC, vC} i := by
  classical
  obtain ⟨⟨cS⟩, huniq⟩ := canonical_small A B A (extensionFunctor i)
    (identityAlgebraicInverseImage A) i (fun _ ↦ rfl) (𝟭 _) Adjunction.id
    (extensionFunctor_mapPresentation i)
  have hunit (M N : Modules.{w, uC, vC} A) (U : Cᵒᵖ)
      (x : M.val.obj U) (y : N.val.obj U) :
      (cS.mu M N).hom.val.app U
        (extensionTmul i ((monoidalCategory A).tensorObj M N) U 1
          (ringedComparisonPure A M N U x y)) =
      ringedComparisonPure B ((extensionFunctor.{w, uC, vC} i).obj M)
        ((extensionFunctor.{w, uC, vC} i).obj N) U
        (extensionTmul i M U 1 x) (extensionTmul i N U 1 y) := by
    have hq (P : Modules.{w, uC, vC} A) (V : Cᵒᵖ) (z : P.val.obj V) :
        (cS.q P).hom.app V z = extensionTmul i P V 1 z := cS.q_one P V z
    let Z := (underlying A).obj M ⨯ (underlying A).obj N
    let x0 : Z ⟶ (underlying A).obj M := prod.fst
    let y0 : Z ⟶ (underlying A).obj N := prod.snd
    let z := CochainTensorComparison.tensorPair A M N Z x0 y0
    let ev := sheafToPresheaf J (Type w) ⋙ (CategoryTheory.evaluation Cᵒᵖ (Type w)).obj U
    obtain ⟨t, hx, hy⟩ := CochainTensorComparison.productElements ev
      ((underlying A).obj M) ((underlying A).obj N) x y
    have hp := cS.pure M N Z x0 y0 z (fun _ _ ↦ rfl) U t
    dsimp only [extensionPullback, identityAlgebraicInverseImage, Iso.refl_inv,
      NatTrans.id_app, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hp
    simp only [Category.id_comp] at hp
    change (cS.mu M N).hom.val.app U ((cS.q _).hom.app U (z.hom.app U t)) =
      ringedComparisonPure B ((extensionFunctor.{w, uC, vC} i).obj M)
        ((extensionFunctor.{w, uC, vC} i).obj N) U
        ((cS.q M).hom.app U (x0.hom.app U t))
        ((cS.q N).hom.app U (y0.hom.app U t)) at hp
    have hz : z.hom.app U t =
        ringedComparisonPure A M N U (x0.hom.app U t) (y0.hom.app U t) := rfl
    change x0.hom.app U t = x at hx
    change y0.hom.app U t = y at hy
    have hz' : z.hom.app U t = ringedComparisonPure A M N U x y :=
      hz.trans (congrArg₂ (ringedComparisonPure A M N U) hx hy)
    exact ((congrArg ((cS.mu M N).hom.val.app U)
      ((hq _ U _).trans (congrArg (extensionTmul i _ U 1) hz'))).symm.trans hp).trans
        (congrArg₂ (ringedComparisonPure B _ _ U)
          ((hq M U _).trans (congrArg (extensionTmul i M U 1) hx))
          ((hq N U _).trans (congrArg (extensionTmul i N U 1) hy)))
  have hf (M N : Modules.{w, uC, vC} A) (U : Cᵒᵖ) :=
    scalar_linear_formulas ((cS.mu M N).hom.val.app U).hom ((cS.mu M N).inv.val.app U).hom
      (iso_hom_inv_apply (cS.mu M N) U)
      (extensionTmul i ((monoidalCategory A).tensorObj M N) U)
      (extensionTmul i M U) (extensionTmul i N U)
      (ringedComparisonPure A M N U) (ringedComparisonPure B _ _ U)
      (extension_scalar i _ U) (extension_scalar i M U) (extension_scalar i N U)
      (fun b x y ↦ (pure_smul _ _ U b x y).1)
      (fun b x y ↦ (pure_smul _ _ U b x y).2) (hunit M N U)
  refine ⟨cS.mu, ⟨⟨fun M N U b x y ↦ (hf M N U).1 b x y,
    fun M N U b c x y ↦ (hf M N U).2 b c x y⟩, cS.naturality, ?_⟩, ?_⟩
  · intro c
    exact congrArg (fun z ↦ z.mu) (huniq.elim c cS)
  · intro t ht
    exact (ht.2.2 cS).symm

private theorem map_extension {A B : Sheaf J CommRingCat.{w}} (i : A ⟶ B)
    (M : Modules.{w, uC, vC} A) (H : Modules.{w, uC, vC} B)
    (f : (extensionFunctor.{w, uC, vC} i).obj M ⟶ H)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    f.val.app U (extensionTmul i M U b x) = b • f.val.app U (extensionTmul i M U 1 x) :=
  (congrArg (f.val.app U) (extension_scalar i M U b x)).trans
    ((f.val.app U).hom.map_smul b _)

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem common_comparisons
    (G : Sheaf K (Type w) ⥤ Sheaf J (Type w))
    (adj : F ⊣ G) [PreservesFiniteLimits F] :
    ∃ (l : common d ≅ left d) (h : common d ≅ right d),
      (∀ (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (b : d.B1.obj.obj U)
          (x : (d.I0.modules.obj M).val.obj U),
        (l.hom.app M).val.app U
          (extensionTmul (d.phi0 ≫ d.iX) (d.I0.modules.obj M) U b x) =
        extensionTmul d.iX ((pull0 d).obj M) U b
          (extensionTmul d.phi0 (d.I0.modules.obj M) U 1 x)) ∧
      (∀ (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (b : d.B1.obj.obj U)
          (x : (d.I0.modules.obj M).val.obj U),
        (h.hom.app M).val.app U
          (extensionTmul (d.phi0 ≫ d.iX) (d.I0.modules.obj M) U b x) =
        extensionTmul d.phi1 (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) U b
          ((transportedInsertion d M).hom.app U x)) := by
  let q0 := fun M : Modules.{w, uC, vC} d.R0 ↦
    insertion.{w, uD, vD} d.phi0 (d.I0.modules.obj M)
  let q1 := fun M : Modules.{w, uC, vC} d.R1 ↦
    insertion.{w, uD, vD} d.phi1 (d.I1.modules.obj M)
  let qc := fun M : Modules.{w, uC, vC} d.R0 ↦
    insertion.{w, uD, vD} (d.phi0 ≫ d.iX) (d.I0.modules.obj M)
  obtain ⟨l, hl⟩ :=
    CochainCompositeHom.normalizedScalarComposition_exists.{w, uC, vC, uD, vD, uD, vD}
    (R := d.R0) (S := d.B0) (T := d.B1)
    F G adj d.A0 d.I0 d.phi0 (pull0 d) (fun _ ↦ rfl)
    (by intros; rfl)
    (𝟭 _) (𝟭 _) Adjunction.id d.B0 (identityAlgebraicInverseImage d.B0) d.iX
    (extensionFunctor.{w, uD, vD} d.iX) (fun _ ↦ rfl) (extensionFunctor_mapPresentation d.iX)
    d.A0 d.I0 (d.phi0 ≫ d.iX) (common d) (fun _ ↦ rfl)
    (by intros; rfl)
    q0 (by
      intro M U x
      exact insertion_section d.phi0 (d.I0.modules.obj M) U x)
    (insertion.{w, uD, vD} d.iX)
    (by
      intro M U x
      exact insertion_section d.iX M U x)
    qc (by
      intro M U x
      exact insertion_section (d.phi0 ≫ d.iX) (d.I0.modules.obj M) U x)
    (by simp only [identityAlgebraicInverseImage, Iso.refl_hom, Functor.id_map,
      Functor.map_comp, Category.assoc, Category.id_comp])
  change common d ≅ left d at l
  obtain ⟨h, hh⟩ :=
    CochainCompositeHom.normalizedScalarComposition_exists.{w, uC, vC, uC, vC, uD, vD}
    (R := d.R0) (S := d.R1) (T := d.B1)
    (𝟭 _) (𝟭 _) Adjunction.id d.R0 (identityAlgebraicInverseImage d.R0) d.iY
    (extensionFunctor.{w, uC, vC} d.iY) (fun _ ↦ rfl) (extensionFunctor_mapPresentation d.iY)
    F G adj d.A1 d.I1 d.phi1 (pull1 d) (fun _ ↦ rfl)
    (by intros; rfl)
    d.A0 d.I0 (d.phi0 ≫ d.iX) (common d) (fun _ ↦ rfl)
    (by intros; rfl)
    (insertion.{w, uC, vC} d.iY)
    (by
      intro M U x
      exact insertion_section d.iY M U x)
    q1 (by
      intro M U x
      exact insertion_section d.phi1 (d.I1.modules.obj M) U x)
    qc (by
      intro M U x
      exact insertion_section (d.phi0 ≫ d.iX) (d.I0.modules.obj M) U x)
    (by
      simp only [identityAlgebraicInverseImage, Iso.refl_hom, Category.id_comp]
      rw [d.commutes, Functor.map_comp, ← Category.assoc, ← d.graph]
      simp only [Category.assoc])
  change common d ≅ right d at h
  refine ⟨l, h, ?_, ?_⟩
  · intro M U b x
    have he := congrArg (fun f ↦
      (d.I0.moduleUnderlying.hom.app M ≫ f).hom.app U x)
        (hl M ((underlying d.R0).obj M) (𝟙 _))
    simp only [Functor.map_id, Functor.id_map, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc, identityAlgebraicInverseImage, Iso.refl_inv,
      NatTrans.id_app] at he
    change (l.hom.app M).val.app U ((qc M).hom.app U x) =
      (insertion.{w, uD, vD} d.iX ((pull0 d).obj M)).hom.app U
        ((q0 M).hom.app U x) at he
    simp only [q0, qc, insertion_section] at he
    exact (map_extension (d.phi0 ≫ d.iX) (d.I0.modules.obj M) _ (l.hom.app M)
      U b x).trans ((congrArg (fun z ↦ b • z) he).trans
        (extension_scalar d.iX ((pull0 d).obj M) U b
          (extensionTmul d.phi0 (d.I0.modules.obj M) U 1 x)).symm)
  · intro M U b x
    have he := congrArg (fun f ↦
      (d.I0.moduleUnderlying.hom.app M ≫ f).hom.app U x)
        (hh M ((underlying d.R0).obj M) (𝟙 _))
    simp only [Functor.map_id, Functor.id_map, Category.id_comp,
      Iso.hom_inv_id_app_assoc, identityAlgebraicInverseImage, Iso.refl_inv,
      NatTrans.id_app] at he
    dsimp only [identityAlgebraicInverseImage, Iso.refl_inv, NatTrans.id_app,
      Functor.id_map, Functor.comp_obj, Functor.id_obj] at he
    simp only [Category.id_comp] at he
    change (h.hom.app M).val.app U ((qc M).hom.app U x) =
      (q1 ((extensionFunctor.{w, uC, vC} d.iY).obj M)).hom.app U
        ((transportedInsertion d M).hom.app U x) at he
    simp only [q1, qc, insertion_section] at he
    exact (map_extension (d.phi0 ≫ d.iX) (d.I0.modules.obj M) _ (h.hom.app M)
      U b x).trans ((congrArg (fun z ↦ b • z) he).trans
        (extension_scalar d.phi1
          (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) U b
          ((transportedInsertion d M).hom.app U x)).symm)

end Proof

/-- Balanced construction of the coefficient/pullback comparison. The two inverse formulas,
all balancing and sheafification descent, naturality, uniqueness and normalization through
one pullback are retained. The scalar comparisons on both X and Y are asserted in the
same conclusion.
Source: Stacks 03EL (auxiliary; not a blueprint node).

Proof: Apply the normalized scalar-composition theorem twice, first to the ringed inverse
image followed by scalar extension along i_X, and then to scalar extension along i_Y
followed by the ringed inverse image. The graph equation and coefficient square give the
same composite coefficient. Evaluating the two normalizations on the identity generalized
section gives the unit-insertion formulas for l and h on all inverse-image sections.
Linearity gives arbitrary scalar coefficients. Set k = l.symm followed by h; scalar
balancing proves both displayed formulas. The sheafification adjunction and scalar-extension
extensionality identify any other normalized l and h with these, proving uniqueness of k.

For each scalar map, use the existing canonical ringed tensor comparison for the identity
geometric morphism. Evaluate its generalized pure formula on the product of the two
underlying module sheaves; evaluation preserves this product, so this covers any pair of
local sections. Its unit normalization gives the coefficient-one formula. Linearity and
tensor bilinearity give the general forward formula; applying the inverse gives its product
of scalar coefficients. Naturality is a field of the canonical comparison. Its uniqueness
identifies every normalized canonical comparison with this one, and the canonical
normalization clause of any second scalar candidate proves uniqueness of the scalar family. -/
theorem coefficientComparisons_balanced_construction (G : Sheaf K (Type w) ⥤ Sheaf J (Type w))
    (adj : F ⊣ G) [PreservesFiniteLimits F] :
    (∃! k : left d ≅ right d, PullbackFormulas d k ∧ ViaCommonPullback d k) ∧
      ScalarTensorConstruction d.iX ∧ ScalarTensorConstruction d.iY := by
  classical
  obtain ⟨l, h, hl, hh⟩ := common_comparisons d G adj
  let k : left d ≅ right d := l.symm ≪≫ h
  have hkl (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (z : ((common d).obj M).val.obj U) :
      (k.hom.app M).val.app U ((l.hom.app M).val.app U z) =
        (h.hom.app M).val.app U z := by
    have he : l.hom ≫ k.hom = h.hom := l.hom_inv_id_assoc h.hom
    exact congrArg (fun f ↦ (f.app M).val.app U z) he
  have hkh (M : Modules.{w, uC, vC} d.R0) (U : Dᵒᵖ) (z : ((common d).obj M).val.obj U) :
      (k.inv.app M).val.app U ((h.hom.app M).val.app U z) =
        (l.hom.app M).val.app U z := by
    have he : h.hom ≫ k.inv = l.hom := h.hom_inv_id_assoc l.hom
    exact congrArg (fun f ↦ (f.app M).val.app U z) he
  have hk : PullbackFormulas d k := by
    constructor
    · intro M U b a x
      have ha := extension_scalar d.phi0 (d.I0.modules.obj M) U a x
      have hb := extension_balance d.iX ((pull0 d).obj M) U b a
        (extensionTmul d.phi0 (d.I0.modules.obj M) U 1 x)
      have hc := congrArg (extensionTmul d.iX ((pull0 d).obj M) U b) ha
      exact (congrArg ((k.hom.app M).val.app U) (hc.trans hb)).trans
        ((congrArg ((k.hom.app M).val.app U)
          (hl M U (b * d.iX.hom.app U a) x).symm).trans
          ((hkl M U _).trans (hh M U (b * d.iX.hom.app U a) x)))
    · intro M U b a x
      have hb := extension_balance d.phi1
        (d.I1.modules.obj ((extensionFunctor.{w, uC, vC} d.iY).obj M)) U b a
        ((transportedInsertion d M).hom.app U x)
      exact (congrArg ((k.inv.app M).val.app U) hb).trans
        ((congrArg ((k.inv.app M).val.app U)
          (hh M U (b * d.phi1.hom.app U a) x).symm).trans
          ((hkh M U _).trans (hl M U (b * d.phi1.hom.app U a) x)))
  refine ⟨⟨k, ⟨hk, ⟨l, h, hl, hh, rfl⟩⟩, ?_⟩,
    scalar_construction d.iX, scalar_construction d.iY⟩
  intro k' hk'
  obtain ⟨l', h', hl', hh', he'⟩ := hk'.2
  have el : l' = l := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply extension_unit_ext (d.phi0 ≫ d.iX) (d.I0.modules.obj M)
    intro U x
    exact (hl' M U 1 x).trans (hl M U 1 x).symm
  have eh : h' = h := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply extension_unit_ext (d.phi0 ≫ d.iX) (d.I0.modules.obj M)
    intro U x
    exact (hh' M U 1 x).trans (hh M U 1 x).symm
  simpa only [el, eh, k] using he'

end CategoryTheory.CoefficientComparisonsBalanced
