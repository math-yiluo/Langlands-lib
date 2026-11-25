/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The comparison isomorphisms of pro-étale pullbacks are monoidal

For sheaves of `ℚ̄_ℓ`-modules on the small pro-étale sites, the composition isomorphism
`(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks, the isomorphism `g^* ≅ g'^*` for `g = g'` and the
isomorphism `(e.hom)^* ≅ (e.inv)_*` for an isomorphism of schemes `e` are monoidal natural
isomorphisms, for the strong monoidal structures of the pullbacks and the lax monoidal
structures of the pushforwards. The first is conjugate to the monoidal composition isomorphism
of pushforwards (`CategoryTheory.isMonoidal_conjugateEquiv_symm`); the last is the comparison
of two left adjoints of `(e.hom)_*`, the second adjunction coming from the equivalence
`(e.hom)_*` with inverse `(e.inv)_*`, whose unit is built from monoidal isomorphisms of
pushforwards (`CategoryTheory.isMonoidal_leftAdjointUniq_hom`).

## Main results

- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarComp_hom`: `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` is
  monoidal.
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarCongr_hom`: `g^* ≅ g'^*` is monoidal.
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarIsoLowerStarInv_hom`: `(e.hom)^* ≅ (e.inv)_*`
  is monoidal.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Comp

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `h₂^* ⋙ h₁^* ≅ (h₁ ≫ h₂)^*` of pullbacks is monoidal: it is
the conjugate of the monoidal composition isomorphism of pushforwards. -/
instance isMonoidal_upperStarComp_inv :
    NatTrans.IsMonoidal (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).inv := by
  have h₁' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (h₁ ≫ h₂))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) h₂).comp
        (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) h₁))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).inv

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of pullbacks is monoidal. -/
instance isMonoidal_upperStarComp_hom :
    NatTrans.IsMonoidal (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).hom :=
  have : NatTrans.IsMonoidal (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).symm.hom :=
    isMonoidal_upperStarComp_inv h₁ h₂
  inferInstanceAs (NatTrans.IsMonoidal (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).symm.inv)

end Comp

section Congr

variable {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')

/-- The isomorphism `g_* ≅ g'_*` of pushforwards along equal morphisms is monoidal. -/
instance isMonoidal_lowerStarCongr_hom :
    NatTrans.IsMonoidal (lowerStarCongr (WeilCoefficients.{u} l) h).hom := by
  subst h
  rw [lowerStarCongr_rfl]
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))

/-- The isomorphism `g^* ≅ g'^*` of pullbacks along equal morphisms is monoidal. -/
instance isMonoidal_upperStarCongr_hom :
    NatTrans.IsMonoidal (upperStarCongr (WeilCoefficients.{u} l) h).hom := by
  subst h
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))

end Congr

section Iso

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The isomorphism `(e.hom)^* ≅ (e.inv)_*` for an isomorphism of schemes `e` is monoidal,
`(e.inv)_*` being strong monoidal. -/
instance isMonoidal_upperStarIsoLowerStarInv_hom :
    NatTrans.IsMonoidal (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom := by
  let : (e.inv)_*[WeilCoefficients.{u} l].Monoidal := .ofLaxMonoidal _
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom)
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  let adj₂ : (e.inv)_*[WeilCoefficients.{u} l] ⊣ (e.hom)_*[WeilCoefficients.{u} l] :=
    (lowerStarEquivalence (WeilCoefficients.{u} l) e).symm.toAdjunction
  have h₂ : NatTrans.IsMonoidal adj₂.unit := by
    change NatTrans.IsMonoidal (lowerStarComp (WeilCoefficients.{u} l) e.inv e.hom ≪≫
      lowerStarCongr (WeilCoefficients.{u} l) e.inv_hom_id ≪≫
        lowerStarId (WeilCoefficients.{u} l) Y).inv
    rw [Iso.trans_inv, Iso.trans_inv]
    infer_instance
  exact isMonoidal_leftAdjointUniq_hom (upperStarLowerStarAdjunction _ e.hom) adj₂

end Iso

end AlgebraicGeometry.ProEtale
