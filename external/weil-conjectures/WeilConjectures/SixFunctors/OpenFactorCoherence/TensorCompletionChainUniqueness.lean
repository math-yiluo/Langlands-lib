/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-! # The two quotient coordinates determine the tensor augmentation

Source: Bhatt--Scholze, Definition 3.4.10; the signed Roos mapping-fibre model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem two_coordinates {C : Type*} [Category* C] [Preadditive C]
    {M N K L : C} (a b : M ⟶ N) (p : N ⟶ K) (q : N ⟶ L)
    (i : K ⟶ N) (j : L ⟶ N) (hid : p ≫ i + q ≫ j = 𝟙 N)
    (hp : a ≫ p = b ≫ p) (hq : a ≫ q = b ≫ q) : a = b := by
  have h := congrArg₂ (fun f g ↦ f ≫ i + g ≫ j) hp hq
  simpa only [Category.assoc, ← Preadditive.comp_add, hid, Category.comp_id] using h

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.monoidalCategory

/-- The pure quotient coordinate and zero shifted coordinate determine the chain map.
Source: Bhatt--Scholze 3.4.10; the explicit Roos augmentation in constructible
tensor completion, step 8
(blueprint: lem-sf-tensor-completion-chain-uniqueness).
Proof: fix the two input complexes and a total degree. A morphism into the
mapping cocone is determined by its first and shifted coordinates. The shifted
coordinates of both maps vanish by the second normalization clause. Project
the first coordinates onto every factor of the countable product. Their
restrictions to every homogeneous total-tensor summand agree on all local
pure tensors by the first clause. Pure tensors generate the presheaf tensor;
sheafification and the coproduct universal property give equality of these
restrictions, then of the first coordinates. Mapping-cocone extensionality
gives equality in every degree, hence equality of the complex morphisms.
Natural-transformation extensionality gives equality of the chain maps.
The same extensionality applies when a summand or the site is empty. -/
theorem tensorCompletionChain_unique
    (a b : constructibleTensorTotal l E X ⟶
      integralOperationsTensorComplexFunctor.{u, u} l E X)
    (ha : IsTensorChain l E X a) (hb : IsTensorChain l E X b) : a = b := by
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  let d := constructibleTensorBoundary l E X P Q
  have hf : a.app (P, Q) ≫ CochainComplex.mappingCocone.fst d =
      b.app (P, Q) ≫ CochainComplex.mappingCocone.fst d := by
    apply Limits.Pi.hom_ext
    intro n
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    subst k
    apply AlgebraicGeometry.Scheme.tensor_hom_ext X
      (completedIntegralCommRingSheafUnrestricted l E X) _ _
    intro V x y
    exact (ha.1 P Q p q n V x y).trans (hb.1 P Q p q n V x y).symm
  apply HomologicalComplex.hom_ext
  intro k
  have hfst := congrArg (fun f ↦ f.f k) hf
  dsimp only [HomologicalComplex.comp_f] at hfst
  have hsnd := (ha.2 P Q k (k + -1) rfl).trans (hb.2 P Q k (k + -1) rfl).symm
  exact two_coordinates _ _ _ _ _ _
    (CochainComplex.mappingCocone.id_X (constructibleTensorBoundary l E X P Q)
      k (k + -1) rfl) hfst hsnd

end WeilConjectures.OpenFactorCoherence
