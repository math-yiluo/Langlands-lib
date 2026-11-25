/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.ConstantFieldPullback
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.FieldCoefficientTateTwist

/-!
# The constant Weil sheaf and its constant twists as pulled-back Weil sheaves

The constant Weil sheaf `ℚ̄_ℓ` on a `k₀`-scheme `X`
(`AlgebraicGeometry.ProEtaleWeilSheaf.adicConstant`) is the constant `ℓ`-adic sheaf on the
geometric fibre `X̄` with the Weil structure `(Fr_X⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` of the constant sheaf. It is
also the pullback `p^* ℚ̄_ℓ,X₀` of the constant sheaf of the model `X₀` along `p : X̄ ⟶ X₀`, with
the canonical Weil structure of pulled-back sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`); the two Weil structures agree
under the identification `p^* ℚ̄_ℓ,X₀ ≅ ℚ̄_ℓ,X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.adicConstantIsoGeometricFiberPullbackUnit`). Hence the
constant twist `ℚ̄_ℓ ⊗ 𝓑_b` is the pullback `p^* ℚ̄_ℓ,X₀` with its canonical Weil structure
multiplied by `b` (`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackTwist`), and so is
the Tate sheaf `ℚ̄_ℓ(1)` with `b = χ_ℓ(σ)`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafOneObjIsoGeometricFiberPullbackTwist`).

This is the native half of the comparison of the Tate twist of Weil complexes with the
roots-of-unity Tate twist of the condensed model, needed by smooth purity
(`AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth`): through
`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso`, the condensed
image of `ℚ̄_ℓ(1)` is the pullback of the condensed unit with its canonical Weil structure
multiplied by `χ_ℓ(σ)`.
-/

@[expose] public section


universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The identifications `g^* ℚ̄_ℓ ≅ ℚ̄_ℓ` are compatible with the factorisation isomorphisms
`g₁^* g₂^* ℚ̄_ℓ ≅ g^* ℚ̄_ℓ` along `g₁ ≫ g₂ = g`. -/
lemma adicUpperStarFactorIso_hom_comp_adicUpperStarUnitIso_hom {X Y Z : Scheme.{u}}
    {g₁ : X ⟶ Y} {g₂ : Y ⟶ Z} {g : X ⟶ Z} (h : g₁ ≫ g₂ = g) :
    (adicUpperStarFactorIso h (AdicSheaf.unit l Z)).hom ≫ (adicUpperStarUnitIso l g).hom =
      (g₁)^*ᵃ[l].map (adicUpperStarUnitIso l g₂).hom ≫ (adicUpperStarUnitIso l g₁).hom := by
  subst h
  have e : (adicUpperStarFactorIso (rfl : g₁ ≫ g₂ = g₁ ≫ g₂) (AdicSheaf.unit l Z)).hom =
      (adicUpperStarComp l g₁ g₂).inv.app _ := by
    simp [adicUpperStarFactorIso, adicUpperStarCongr]
  rw [e, ← adicUpperStarUnitIso_comp, Iso.inv_hom_id_app_assoc]

end ProEtale

open ProEtale

namespace ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The Weil structure of the constant Weil sheaf, unfolded. -/
lemma adicConstant_obj_str :
    (adicConstant k₀ l X).obj.str =
      (adicLowerStarUnitIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom :=
  rfl

/-- The Weil structure of the pulled-back constant sheaf, unfolded. -/
lemma geometricFiberPullback_obj_unit_obj_str :
    ((geometricFiberPullback k₀ l X).obj (AdicSheaf.unit l X)).obj.str =
      ((geometricFiberPullbackFrobeniusIso k₀ l X).app (AdicSheaf.unit l X)).hom :=
  (IsoAlgebra.str_hom _).symm.trans
    (congrArg Iso.hom (geometricFiberPullback_obj_str k₀ l X (AdicSheaf.unit l X)))

/-- The Weil structure of the constant sheaf and the canonical Weil structure of the pulled-back
constant sheaf agree under `p^* ℚ̄_ℓ,X₀ ≅ ℚ̄_ℓ,X̄`. -/
lemma frobeniusPullback_map_adicUpperStarUnitIso_inv_comp :
    (WeilSheaf.frobeniusPullback k₀ l X).map
        (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv ≫
        ((geometricFiberPullbackFrobeniusIso k₀ l X).app (AdicSheaf.unit l X)).hom =
      (adicLowerStarUnitIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom ≫
        (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv := by
  have h1 : (adicLowerStarUnitIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom =
      (adicUpperStarIsoLowerStarInv l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ ≫
        (adicUpperStarUnitIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom := by
    rw [← adicUpperStarIsoLowerStarInv_hom_app_unit_comp, Iso.inv_hom_id_app_assoc]
  have h2 : (WeilSheaf.frobeniusPullback k₀ l X).map
        (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv ≫
        (adicUpperStarIsoLowerStarInv l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ =
      (adicUpperStarIsoLowerStarInv l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
          (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).inv :=
    (adicUpperStarIsoLowerStarInv l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.naturality _
  rw [geometricFiberPullbackFrobeniusIso_hom_app, h1, ← Category.assoc, h2]
  simp only [Category.assoc]
  refine (cancel_epi _).2 ?_
  rw [← cancel_mono (adicUpperStarUnitIso l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    adicUpperStarFactorIso_hom_comp_adicUpperStarUnitIso_hom, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The constant Weil sheaf is pulled back from the model**: the constant Weil sheaf `ℚ̄_ℓ`
on `X` is the pullback `p^* ℚ̄_ℓ,X₀` of the constant sheaf of the model along `p : X̄ ⟶ X₀`, with
its canonical Weil structure, under the identification `p^* ℚ̄_ℓ,X₀ ≅ ℚ̄_ℓ,X̄`. -/
noncomputable def adicConstantIsoGeometricFiberPullbackUnit :
    adicConstant k₀ l X ≅ (geometricFiberPullback k₀ l X).obj (AdicSheaf.unit l X) :=
  IsoAlgebra.isoMk
    (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).symm (by
    rw [Iso.symm_hom, geometricFiberPullback_obj_unit_obj_str, adicConstant_obj_str]
    exact frobeniusPullback_map_adicUpperStarUnitIso_inv_comp k₀ l X)

/-- The pulled-back constant sheaf with its canonical Weil structure multiplied by `b` is the
constant twist of the pulled-back constant sheaf, as objects. -/
lemma mk_geometricFiberPullback_str_trans_smulIso_eq (b : (PadicAlgCl l)ˣ) :
    IsoAlgebra.mk ((geometricFiberPullback k₀ l X).obj (AdicSheaf.unit l X)).carrier
        (((geometricFiberPullback k₀ l X).obj (AdicSheaf.unit l X)).str ≪≫
          WeilCoefficients.smulIso b _) =
      geometricFiberPullbackTwist k₀ l X (AdicSheaf.unit l X) b := by
  rw [geometricFiberPullback_obj_str]
  rfl

/-- **Constant twists of the constant Weil sheaf are pulled back from the model**: the constant
twist `ℚ̄_ℓ ⊗ 𝓑_b` is the pullback `p^* ℚ̄_ℓ,X₀` with its canonical Weil structure multiplied
by `b`. -/
noncomputable def constantTwistAdicConstantIsoGeometricFiberPullbackTwist (b : (PadicAlgCl l)ˣ) :
    (constantTwist k₀ l X b).obj (adicConstant k₀ l X) ≅
      geometricFiberPullbackTwist k₀ l X (AdicSheaf.unit l X) b :=
  (constantTwist k₀ l X b).mapIso (adicConstantIsoGeometricFiberPullbackUnit k₀ l X) ≪≫
    (mkConstantTwistIso k₀ l X _ b).symm ≪≫
    eqToIso (mk_geometricFiberPullback_str_trans_smulIso_eq k₀ l X b)

end ProEtaleWeilSheaf

namespace WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant twist `ℚ̄_ℓ ⊗ 𝓑_b` of the constant Weil sheaf is the pullback `p^* ℚ̄_ℓ,X₀`
with its canonical Weil structure multiplied by `b`. -/
noncomputable def constantTwistAdicConstantObjIsoGeometricFiberPullbackTwist
    (b : (PadicAlgCl l)ˣ) :
    ((adicConstant k₀ l X).constantTwist b).obj ≅
      ProEtaleWeilSheaf.geometricFiberPullbackTwist k₀ l X (AdicSheaf.unit l X) b :=
  constantTwistObjIso (adicConstant k₀ l X) b ≪≫
    ProEtaleWeilSheaf.constantTwistAdicConstantIsoGeometricFiberPullbackTwist k₀ l X b

/-- **The Tate sheaf `ℚ̄_ℓ(1)` is pulled back from the model**: it is the pullback
`p^* ℚ̄_ℓ,X₀` of the constant sheaf with its canonical Weil structure multiplied by the
cyclotomic unit `χ_ℓ(σ)`. -/
noncomputable def tateTwistSheafOneObjIsoGeometricFiberPullbackTwist :
    (tateTwistSheaf k₀ l X 1).obj ≅
      ProEtaleWeilSheaf.geometricFiberPullbackTwist k₀ l X (AdicSheaf.unit l X)
        (cyclotomicUnit k₀ l) :=
  constantTwistAdicConstantObjIsoGeometricFiberPullbackTwist k₀ l X (cyclotomicUnit k₀ l)

end WeilSheaf

end AlgebraicGeometry
