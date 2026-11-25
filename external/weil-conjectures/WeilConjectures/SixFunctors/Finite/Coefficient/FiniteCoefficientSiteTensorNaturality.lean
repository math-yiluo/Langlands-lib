/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteChainTensor
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicChainTensor
/-! # Naturality of normalized finite coefficient total tensor comparisons -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a b v w c
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Signed total tensor, shared before specializing the module category of a site.
It is definitionally `coefficientTotalTensor` at a ringed site (see `target_total_eq`).
Source: Stacks 06YN, 07A4 (blueprint: lem-sf-finite-coefficient-site-tensor-naturality). -/
noncomputable def coefficientTotalTensorGeneral
    (D : Type a) [Category.{b} D] [Preadditive D] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex D ℤ,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor D) (.up ℤ)] :
    CochainComplex D ℤ × CochainComplex D ℤ ⥤ CochainComplex D ℤ :=
  Functor.uncurry.obj ((curriedTensor D).map₂CochainComplex)

/-- Naturality of a specified tensor-comparison family, with all functor data shared.
Source: Stacks 06YN and 07A4
(blueprint: lem-sf-finite-coefficient-site-tensor-naturality). -/
def FiniteHomChainTensorNaturalityAux
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{c} D]
    (U : C ⥤ D) (t : C × C ⥤ C) (t' : D × D ⥤ D)
    {V : C → C → Type c} (ε : ∀ x y, V x y) : Prop :=
  ∃ B : t ⋙ U ≅ U.prod U ⋙ t', ∀ x y, HEq (B.app (x, y)) (ε x y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem total_map_eq
    {B : Type b} [Category.{c} B] [Preadditive B]
    (F : B ⥤ B ⥤ B) [F.PreservesZeroMorphisms]
    [∀ M, (F.obj M).PreservesZeroMorphisms]
    [∀ V W : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctor V W F (.up ℤ)]
    {P Q P' Q' : CochainComplex B ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj (F.map₂CochainComplex)).map (X := (P, Q)) (Y := (P', Q')) (f, g) =
      HomologicalComplex.mapBifunctorMap f g F (.up ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hk
  change HomologicalComplex.ιMapBifunctor P Q F _ i j k hk ≫
    ((HomologicalComplex.mapBifunctorMap f (𝟙 Q) F (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g F (.up ℤ)).f k) = _
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f]
  rw [(F.obj _).map_id, F.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

section Generic
variable {C : Type a} {D : Type b} [Category.{v} C] [Category.{c} D]
  [Preadditive C] [HasZeroObject C] [HasColimitsOfSize.{0, 0} C] [Preadditive D]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
  [(curriedTensor D).PreservesZeroMorphisms]
  [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
  [HasColimitsOfSize.{0, 0} D]
  (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem natural_total_lift
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (N : (FiniteCoefficientTotalComparison.Ordinary G) → Prop) (he : N e) :
    ∃ B : finiteHomCochainTensorGeneral C ⋙ G.mapHomologicalComplex (.up ℤ) ≅
        (G.mapHomologicalComplex (.up ℤ)).prod (G.mapHomologicalComplex (.up ℤ)) ⋙
          coefficientTotalTensorGeneral D,
      ∀ P Q, FiniteCoefficientTotalComparison.Normalization G N P Q
        (B.app (P, Q)) := by
  refine ⟨NatIso.ofComponents (fun PQ ↦ liftTensorIso G e PQ.1 PQ.2) ?_, ?_⟩
  · intro PQ RS f
    dsimp only [coefficientTotalTensorGeneral, Functor.comp_map, Functor.prod_map]
    rw [total_map_eq]
    simpa only [finiteHomCochainTensorGeneral, liftTensorIso, asIso_hom,
      HomologicalComplex.tensorHom] using
      HomologicalComplex.mapBifunctorComparison_naturality
        (curryTensorComparison G e) (.up ℤ) f.1 f.2
  · intro P Q
    exact ⟨e, he, liftTensorIso_ι G e P Q⟩
private theorem natural_total_chosen
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (N : (FiniteCoefficientTotalComparison.Ordinary G) → Prop)
    (he : N e)
    (H : ∀ P Q : CochainComplex C ℤ,
      ∃! a, FiniteCoefficientTotalComparison.Normalization G N P Q a) :
    FiniteHomChainTensorNaturalityAux (G.mapHomologicalComplex (.up ℤ))
      (finiteHomCochainTensorGeneral C)
      (coefficientTotalTensorGeneral D)
      (fun P Q ↦ (H P Q).choose) := by
  unfold FiniteHomChainTensorNaturalityAux
  obtain ⟨B, hB⟩ := natural_total_lift G e N he
  exact ⟨B, fun P Q ↦ heq_of_eq ((H P Q).choose_spec.2 _ (hB P Q))⟩
end Generic

attribute [local irreducible] ProEtale.finiteCoefficientIntrinsicComparison
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  ProEtale.comparisonUpperStar ProEtale.finiteCoefficientIntrinsicRealization
  PresheafOfModules.sheafification presheafToSheaf
  Functor.mapHomologicalComplex ProEtale.FiniteCoefficientTensorNormalization
  FiniteCoefficientTotalComparison.Normalization FiniteCoefficientTotalComparison.Ordinary
  FiniteHomChainTensorNaturalityAux

private theorem target_total_eq (X : Scheme.{u}) (A : Type u) [CommRing A] :
    letI : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    letI := ProEtale.finiteCoefficientIntrinsicMonoidal X A
    coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (Scheme.proEtaleConstantRing X A) =
      coefficientTotalTensorGeneral
        (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) := by
  rfl

private theorem natural_total_ring (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    letI : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    letI := ProEtale.finiteCoefficientIntrinsicMonoidal X A
    FiniteHomChainTensorNaturalityAux
      ((ProEtale.finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex (.up ℤ))
      (finiteHomCochainTensorGeneral _)
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (Scheme.proEtaleConstantRing X A))
      (ProEtale.finiteCoefficientIntrinsicChainTensor X A) := by
  rw [target_total_eq X A]
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let := ProEtale.finiteCoefficientIntrinsicMonoidal X A
  have := ProEtale.nu_preservesColimits X A
  have : HasColimitsOfSize.{0, 0}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) := inferInstance
  obtain ⟨e, he⟩ := ProEtale.finiteCoefficientIntrinsicTensor_generators X A
  exact natural_total_chosen (ProEtale.finiteCoefficientIntrinsicComparison X A) e
    (ProEtale.FiniteCoefficientTensorNormalization X A) he
    (fun P Q ↦ ProEtale.finiteCoefficientIntrinsicChainTensor_existsUnique X A P Q)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The chosen pure-tensor chain comparisons assemble into a natural isomorphism.
Source: blueprint site comparison paragraph; Stacks 00YV, 06YN and 07A4
(blueprint: lem-sf-finite-coefficient-site-tensor-naturality).

Proof: choose the ordinary natural tensor comparison normalized on local pure tensors.
Lift it to signed total complexes by the total-bifunctor comparison. This lift is
natural in both complexes, is invertible componentwise, and satisfies the prescribed
map on every summand. Hence each component satisfies the normalization that uniquely
characterizes the chosen chain comparison. Uniqueness identifies the components.
The construction is componentwise and includes zero complexes and the empty site. -/
theorem finiteHomNuChainTensor_naturalIso (n : ℕ) :
    FiniteHomChainTensorNaturalityAux (finiteHomNuComplex l E X n)
      (finiteHomCochainTensorGeneral _)
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n))
      (finiteHomNuChainTensor l E X n) := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  unfold finiteHomNuComplex finiteHomNuOrdinary finiteHomNuChainTensor
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact natural_total_ring X (Padic.coefficientExtensionRing l E (n + 1))

end WeilConjectures
