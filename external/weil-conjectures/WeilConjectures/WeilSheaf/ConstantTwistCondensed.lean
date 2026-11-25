/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelScalar
public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.WeilSheaf.ConstantGeometricFiberPullback

/-!
# Constant twists of the constant Weil sheaf in the condensed model

Through the comparison `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` of the two models of
Weil sheaves, the constant Weil sheaf `ℚ̄_ℓ` becomes the regular module `ℚ̲̄_ℓ,X̄` with a Weil
structure `(Fr_X⁻¹)_* ℚ̲̄_ℓ,X̄ ≅ ℚ̲̄_ℓ,X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.adicConstantCondensedStr`), and its constant twist
`ℚ̄_ℓ ⊗ 𝓑_b` by a unit `b ∈ ℚ̄_ℓˣ` becomes the regular module with that Weil structure
multiplied by the constant global section `b`
(`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensedObjConstantTwistAdicConstantIso`): the
comparison of the two models is `ℚ̄_ℓ`-linear on the unit
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom`).
In particular this is the condensed image of the Tate sheaf `ℚ̄_ℓ(1)`, with `b = χ_ℓ(σ)`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by the constant global section `b ∈ ℚ̄_ℓˣ` on the regular module
`ℚ̲̄_ℓ,X̄` of the condensed model, as an automorphism. -/
noncomputable def regularSmulIso (b : (PadicAlgCl l)ˣ) :
    Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) where
  hom := (Mod.regularEndRingHom (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
    (Profinite.PadicAlgCl.constRingHom l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    (b : PadicAlgCl l))).asHom
  inv := (Mod.regularEndRingHom (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
    (Profinite.PadicAlgCl.constRingHom l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    ((b⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l))).asHom
  hom_inv_id := by
    rw [← End.mul_asHom, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rfl
  inv_hom_id := by
    rw [← End.mul_asHom, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rfl

omit [Finite k₀] in
@[simp]
lemma regularSmulIso_hom (b : (PadicAlgCl l)ˣ) :
    (regularSmulIso k₀ l X b).hom =
      (Mod.regularEndRingHom (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
        (Profinite.PadicAlgCl.constRingHom l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        (b : PadicAlgCl l))).asHom :=
  rfl

/-- The Weil structure of the condensed image of a pro-étale Weil sheaf, unfolded. -/
lemma toCondensed_obj_obj_str (F : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensed k₀ l X).obj F).obj.str =
      (condensedFrobeniusComparison k₀ l X).hom.app F.carrier ≫
        (adicSheafEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map F.obj.str :=
  (IsoAlgebra.str_hom _).symm.trans (congrArg Iso.hom (toCondensed_obj_str k₀ l X F))

omit [Finite k₀] in
/-- **The comparison of the two models is `ℚ̄_ℓ`-linear on the unit**, solved for the image of
the multiplication by `b`: `E (b • -) = u ≫ (b •) ≫ u⁻¹` along `u : E ℚ̄_ℓ,X̄ ≅ ℚ̲̄_ℓ,X̄`. -/
lemma adicSheafEquivCondensedMod_functor_map_smul_unit (b : (PadicAlgCl l)ˣ) :
    (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map
        (AdicSheaf.smul (ULift.up (b : PadicAlgCl l))
          (AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) =
      (adicSheafEquivCondensedModUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom ≫
        (regularSmulIso k₀ l X b).hom ≫
        (adicSheafEquivCondensedModUnitIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inv := by
  rw [regularSmulIso_hom, ← adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The Weil structure of the condensed image of the constant Weil sheaf `ℚ̄_ℓ`, transported to
the regular module `ℚ̲̄_ℓ,X̄` along `E ℚ̄_ℓ,X̄ ≅ ℚ̲̄_ℓ,X̄`. -/
noncomputable def adicConstantCondensedStr :
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).mapIso
      (adicSheafEquivCondensedModUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).symm ≪≫
    ((toCondensed k₀ l X).obj (adicConstant k₀ l X)).str ≪≫
    adicSheafEquivCondensedModUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber

lemma adicConstantCondensedStr_hom :
    (adicConstantCondensedStr k₀ l X).hom =
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).map
          (adicSheafEquivCondensedModUnitIso l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inv ≫
        ((toCondensed k₀ l X).obj (adicConstant k₀ l X)).obj.str ≫
        (adicSheafEquivCondensedModUnitIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom :=
  rfl

/-- **The constant Weil sheaf in the condensed model**: `E ℚ̄_ℓ` is the regular module
`ℚ̲̄_ℓ,X̄` with the transported Weil structure. -/
noncomputable def toCondensedObjAdicConstantIso :
    (toCondensed k₀ l X).obj (adicConstant k₀ l X) ≅
      IsoAlgebra.mk _ (adicConstantCondensedStr k₀ l X) :=
  IsoAlgebra.isoMk
    (adicSheafEquivCondensedModUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (by
    have hmk : (IsoAlgebra.mk _ (adicConstantCondensedStr k₀ l X)).obj.str =
        (adicConstantCondensedStr k₀ l X).hom := rfl
    rw [hmk, adicConstantCondensedStr_hom, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp])

/-- **Constant twists of the constant Weil sheaf in the condensed model**: `E (ℚ̄_ℓ ⊗ 𝓑_b)` is
the regular module `ℚ̲̄_ℓ,X̄` with the transported Weil structure of `ℚ̄_ℓ` multiplied by the
constant global section `b`. -/
noncomputable def toCondensedObjConstantTwistAdicConstantIso (b : (PadicAlgCl l)ˣ) :
    (toCondensed k₀ l X).obj ((constantTwist k₀ l X b).obj (adicConstant k₀ l X)) ≅
      IsoAlgebra.mk _ (adicConstantCondensedStr k₀ l X ≪≫ regularSmulIso k₀ l X b) :=
  IsoAlgebra.isoMk
    (adicSheafEquivCondensedModUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (by
    have hmk : (IsoAlgebra.mk _ (adicConstantCondensedStr k₀ l X ≪≫
        regularSmulIso k₀ l X b)).obj.str =
        (adicConstantCondensedStr k₀ l X).hom ≫ (regularSmulIso k₀ l X b).hom := rfl
    have ht : ((constantTwist k₀ l X b).obj (adicConstant k₀ l X)).obj.str =
        (adicConstant k₀ l X).obj.str ≫ AdicSheaf.smul (ULift.up (b : PadicAlgCl l))
          (AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
      dsimp only [constantTwist]
      rw [IsoAlgebra.twist_obj_obj_str, frobeniusPullbackSmulIso_hom_app]
      exact AdicSheaf.smul_comp _ _
    rw [hmk, toCondensed_obj_obj_str, ht, Functor.map_comp,
      adicSheafEquivCondensedMod_functor_map_smul_unit, adicConstantCondensedStr_hom,
      toCondensed_obj_obj_str]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl)

end ProEtaleWeilSheaf

namespace WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- **The Tate sheaf `ℚ̄_ℓ(1)` in the condensed model**: `E ℚ̄_ℓ(1)` is the regular module
`ℚ̲̄_ℓ,X̄` with the transported Weil structure of `ℚ̄_ℓ` multiplied by the cyclotomic unit
`χ_ℓ(σ)`. -/
noncomputable def toCondensedObjTateTwistSheafOneIso :
    (ProEtaleWeilSheaf.toCondensed k₀ l X).obj (tateTwistSheaf k₀ l X 1).obj ≅
      IsoAlgebra.mk _ (ProEtaleWeilSheaf.adicConstantCondensedStr k₀ l X ≪≫
        ProEtaleWeilSheaf.regularSmulIso k₀ l X (cyclotomicUnit k₀ l)) :=
  (ProEtaleWeilSheaf.toCondensed k₀ l X).mapIso
      (constantTwistObjIso (adicConstant k₀ l X) (cyclotomicUnit k₀ l)) ≪≫
    ProEtaleWeilSheaf.toCondensedObjConstantTwistAdicConstantIso k₀ l X (cyclotomicUnit k₀ l)

end WeilSheaf

end AlgebraicGeometry
