/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence

/-!
# Equivariant pullbacks of `ℓ`-adic sheaves

Let `Y` be a scheme over a finite field `L` with geometric fiber `Ȳ` and geometric Galois
Frobenius `Fr_Y`, and let `j : Ȳ ⟶ Z` be a morphism with `j ≫ g = Fr_Y ≫ j` for an automorphism
`g` of `Z`. Pulling back along `j` carries `ℓ`-adic sheaves `A` on `Z` with a structure
`g^* A ≅ A` to Weil sheaves on `Y` over `L`
(`AlgebraicGeometry.ProEtaleWeilSheaf.equivariantPullback`), through the exchange isomorphism
`j^* ∘ Fr_Y^* ≅ g^* ∘ j^*` (`AlgebraicGeometry.adicUpperStarCompFrobeniusIsoOfComm`), which we
describe on the underlying sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The structure isomorphism of the transport of the algebra `(a, Φ)`. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso_obj_mk_str {C D : Type*}
    [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L) (a : C)
    (Φ : F.obj a ≅ a) :
    ((IsoAlgebra.mapOfNatIso e).obj (IsoAlgebra.mk a Φ)).str = e.app a ≪≫ L.mapIso Φ :=
  Iso.ext rfl

-- Stated for arbitrary `a`, `b` and `c`, as `AlgebraicGeometry.ProEtale.exchange_hom_app_hom`,
-- with a proof comparing the morphism terms by `rfl`: for the geometric Frobenii the kernel may
-- time out otherwise.
private lemma exchange_hom_app_hom' {X Y : Scheme.{u}} (j : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (c : a.hom ≫ j = j ≫ b.hom) (M : AdicSheaf l Y) :
    ((Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*ᵃ[l].obj M).X ≫
        (upperStarComp _ a.hom j).inv.app M.X ≫ (upperStarCongr _ c).hom.app M.X ≫
        (upperStarComp _ j b.hom).hom.app M.X ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M.X) := by
  have e₁ := adicUpperStarIsoLowerStarInv_inv_app_hom a ((j)^*ᵃ[l].obj M)
  have e₂ := adicUpperStarComp_inv_app_hom a.hom j M
  have e₃ := adicUpperStarCongr_hom_app_hom c M
  have e₄ := adicUpperStarComp_hom_app_hom j b.hom M
  have e₅ := congrArg (j)^*[WeilCoefficients.{u} l].map
    (adicUpperStarIsoLowerStarInv_hom_app_hom b M)
  refine Eq.trans ?_ (Eq.trans (congrArg₂ (· ≫ ·) e₁ (congrArg₂ (· ≫ ·) e₂
    (congrArg₂ (· ≫ ·) e₃ (congrArg₂ (· ≫ ·) e₄ e₅)))) ?_) <;> rfl

section Equivariant

variable {L : Type u} [Field L] [Finite L] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))]
  {Z : Scheme.{u}} (g : Aut Z) (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ Z)
  (hj : j ≫ g.asIso.hom = (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)

/-- The exchange isomorphism `j^* ∘ Fr_Y^* ≅ g^* ∘ j^*` of pullbacks of `ℓ`-adic sheaves, from
`Fr_Y ≫ j = j ≫ g`, with the pullbacks along automorphisms realized as pushforwards along their
inverses. -/
noncomputable def adicUpperStarCompFrobeniusIsoOfComm :
    (j)^*ᵃ[l] ⋙ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ≅
      (g.asIso.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _
      (adicUpperStarIsoLowerStarInv l
        (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l hj.symm ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l g.asIso) _

private lemma adicUpperStarCompFrobeniusIsoOfComm_eq :
    adicUpperStarCompFrobeniusIsoOfComm g j hj =
      Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l
          (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso).symm ≪≫
        (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l hj.symm ≪≫
        adicUpperStarComp l _ _ ≪≫
        Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l g.asIso) _ :=
  rfl

/-- The exchange isomorphism `j^* ∘ Fr_Y^* ≅ g^* ∘ j^*`, on the underlying sheaves:
`Fr_Y^* j^* ≅ (Fr_Y ≫ j)^* = (j ≫ g)^* ≅ j^* g^*`, with `e^* = (e⁻¹)_*`. -/
lemma adicUpperStarCompFrobeniusIsoOfComm_hom_app_hom (M : AdicSheaf l Z) :
    ((adicUpperStarCompFrobeniusIsoOfComm g j hj).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
          (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso).inv.app
          ((j)^*ᵃ[l].obj M).X ≫
        (upperStarComp _ (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom j).inv.app
          M.X ≫ (upperStarCongr _ hj.symm).hom.app M.X ≫
        (upperStarComp _ j g.asIso.hom).hom.app M.X ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) g.asIso).hom.app M.X) :=
  (congrArg (fun i ↦ (i.hom.app M).hom) (adicUpperStarCompFrobeniusIsoOfComm_eq g j hj)).trans
    (exchange_hom_app_hom' j _ g.asIso hj.symm M)

/-- The pullback along `j : Ȳ ⟶ Z` of `ℓ`-adic sheaves `A` on `Z` with a structure
`g^* A ≅ A`, for an automorphism `g` of `Z` with `j ≫ g = Fr_Y ≫ j`: the sheaf `j^* A` with the
Weil structure `Fr_Y^* j^* A ≅ j^* g^* A ≅ j^* A`. -/
noncomputable def ProEtaleWeilSheaf.equivariantPullback :
    IsoAlgebra ((g.asIso.inv)_*ᵃ[l]) ⥤ ProEtaleWeilSheaf L l Y :=
  IsoAlgebra.mapOfNatIso (adicUpperStarCompFrobeniusIsoOfComm g j hj)

end Equivariant

end AlgebraicGeometry
