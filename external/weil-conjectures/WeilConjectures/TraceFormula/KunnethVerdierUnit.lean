/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom
public import WeilConjectures.TraceFormula.KunnethVerdierDual

/-!
# The Künneth–Verdier map at the unit

For `N = ℚ̄_ℓ,Y` the Künneth–Verdier map `κ_{M,ℚ̄_ℓ} : M ⊠ ω_Y ⟶ RHom(ℚ̄_ℓ, Rp_X^! M)` is the
exceptional Künneth map `α` followed by `Rp_X^! M ≅ RHom(ℚ̄_ℓ, Rp_X^! M)`, up to isomorphisms
(`ProEtale.CondensedRing.kunnethVerdierMap_eq`): `κ_{M,ℚ̄_ℓ}` is an isomorphism if and only if
`α` is (`ProEtale.CondensedRing.isIso_kunnethVerdierMap_unit_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C₁ C₂ C : Type*} [Category C₁] [MonoidalCategory C₁] [MonoidalClosed C₁]
  [Category C₂] [MonoidalCategory C₂] [MonoidalClosed C₂]
  [Category C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  (P : C₁ ⥤ C) (Q : C₂ ⥤ C) [P.Monoidal] [Q.Monoidal]

/-- The external Hom map is an isomorphism when the sources have left duals. -/
lemma isIso_externalHomMap_of_exactPairing (D₁' E₁ L₁ : C₁) (D₂' E₂ L₂ : C₂)
    [ExactPairing D₁' E₁] [ExactPairing D₂' E₂] :
    IsIso (externalHomMap P Q E₁ L₁ E₂ L₂) := by
  rw [externalHomMap_eq_externalIhomMap]
  exact MonoidalClosed.isIso_externalIhomMap_of_exactPairing P Q D₁' E₁ L₁ D₂' E₂ L₂

omit [BraidedCategory C] in
/-- If the transposed form `κ = (u ≫ β ≫ v) ≫ RHom(1, a)` of a map at the unit is an isomorphism,
for isomorphisms `u`, `β`, `v`, then so is `a`: the internal hom out of an object isomorphic to
the unit is isomorphic to the identity functor. -/
lemma isIso_of_isIso_comp_ihom_map {A B T : C} (e : A ≅ 𝟙_ C) (a : B ⟶ T) {S : C}
    {w : S ⟶ (ihom A).obj B} [IsIso w] (h : IsIso (w ≫ (ihom A).map a)) : IsIso a := by
  have : IsIso ((ihom A).map a) := IsIso.of_isIso_comp_left w _
  let φ : 𝟭 C ≅ ihom A := unitNatIso ≪≫ asIso (pre e.hom)
  exact (NatIso.isIso_map_iff φ a).2 this

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The Künneth–Verdier map at the unit**: `κ_{M,ℚ̄_ℓ}` is an isomorphism if and only if the
exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp_X^! M` is. -/
theorem isIso_kunnethVerdierMap_unit_iff (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (kunnethVerdierMap ℓ M (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) ↔
      IsIso (exceptionalKunnethMap ℓ (Y := Y) M) := by
  have := isIso_externalHomMap_of_exactPairing
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) (𝟙_ _) (𝟙_ _) M (𝟙_ _) (𝟙_ _)
    (dualizingComplex' ℓ Y)
  rw [kunnethVerdierMap_eq]
  constructor
  · intro h
    exact isIso_of_isIso_comp_ihom_map
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y))).symm
      _ h
  · intro h
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
