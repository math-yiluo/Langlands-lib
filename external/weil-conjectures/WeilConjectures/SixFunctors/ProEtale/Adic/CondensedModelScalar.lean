/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear
public import WeilConjectures.TraceFormula.WeilScalarUnit

/-!
# The comparison of the two models of `ℓ`-adic sheaves is `ℚ̄_ℓ`-linear

The equivalence `E : AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`) sends the multiplication by a scalar
`c ∈ ℚ̄_ℓ` on the constant sheaf `ℚ̄_ℓ,X` to the multiplication by the constant global section
`c` of the condensed coefficient ring `ℚ̲̄_ℓ,X = p_X^* ℚ̲̄_ℓ`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom`).
Indeed the coefficient comparison `ℚ̲̄_ℓ,X ≅ forgetAb ℚ̄_ℓ,X` sends the constant section `c` to the
constant function `c` 
(`AlgebraicGeometry.ProEtale.constRingHom_hom_comp_condensedRingObjIsoForgetAb_hom`),
as is checked on the profinite test objects, where it is the inclusion of the bounded functions
(`AlgebraicGeometry.ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso_test`).

On the spectrum of a separably closed field, through `End (𝟙_ Mod_{Spec Ω}) ≅ ℚ̄_ℓ`, the image of
the multiplication by `c` is `c` itself
(`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_adicSheafEquivCondensedMod_map_smul`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The adjunction `p_X^* ⊣ p_{X*}` between condensed abelian groups and abelian sheaves on
`X_proét`. -/
noncomputable abbrev upperStarFromPointAdj (X : Scheme.{u}) :
    upperStarFromPoint X ⊣ (ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar) :=
  pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The adjoint of the coefficient comparison `ℚ̲̄_ℓ,X ≅ forgetAb ℚ̄_ℓ,X` sends the constant section
`a` of `ℚ̲̄_ℓ` over a profinite set `S` to the constant function `a` over the test object
`X[S]`. -/
lemma upperStarFromPointAdj_homEquiv_condensedRingObjIsoForgetAb_hom_app (X : Scheme.{u})
    (S : Profinite.{u}) (a : PadicAlgCl l) :
    (((upperStarFromPointAdj X).homEquiv _ _ (condensedRingObjIsoForgetAb l X).hom).hom.app
        (op S)) (Profinite.PadicAlgCl.constSectionRingHom l (op S) a) =
      AdicSheaf.constScalarSection (op ((profiniteToProEtOf X).obj S)) (ULift.up a) := by
  have h : (condensedRingObjIsoForgetAb l X).hom =
      (CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf X l := rfl
  rw [h, Adjunction.homEquiv_naturality_right]
  have ht := CondensedQbarCoefficientRealization.globalCoefficientIso_test l X S
    ⟨ContinuousMap.const S a, IntermediateField.adjoin ℚ_[l] {a},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a),
      fun _ ↦ IntermediateField.mem_adjoin_simple_self ℚ_[l] a⟩
  have hi := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_padicAlgClSheafToAdicConstantSheaf l X) (op ((profiniteToProEtOf X).obj S)))
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply, ht]
  erw [hi]
  rfl

/-- **The coefficient comparison sends constants to constants**: the isomorphism of ring objects
`ℚ̲̄_ℓ,X ≅ forgetAb ℚ̄_ℓ,X` sends the constant global section `c` of `ℚ̲̄_ℓ,X = p_X^* ℚ̲̄_ℓ` to the
constant function `c`, that is to the image of the unit under the multiplication by `c`. -/
lemma constRingHom_hom_comp_condensedRingObjIsoForgetAb_hom (X : Scheme.{u}) (c : PadicAlgCl l) :
    (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
        (Profinite.PadicAlgCl.constRingHom l) X c).hom ≫ (condensedRingObjIsoForgetAb l X).hom =
      (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
          (Profinite.PadicAlgCl.constRingHom l) X 1).hom ≫ (condensedRingObjIsoForgetAb l X).hom ≫
        (weilCoefficientsForgetAb l X).map (ULift.up.{u + 1} c • 𝟙 (adicConstantSheaf l X)) := by
  simp only [CondensedRing.constRingHom_hom, Category.assoc]
  refine congrArg (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ ·) ?_
  apply ((upperStarFromPointAdj X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  apply Sheaf.hom_ext_of_ε_comp
  apply Profinite.natTrans_ext_of_app_one
  have hx (a : PadicAlgCl l) :
      Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
          (Profinite.PadicAlgCl.constRingHom l a).hom =
      ((Profinite.padicAlgClCondensedRing l).obj.ringHomΓCompForget₂
        (Profinite.PadicAlgCl.constSectionRingHom l) (fun _ _ ↦ rfl) a).hom :=
    Sheaf.ε_comp_ringHomΓSheafCompose_hom (coherentTopology Profinite.{u})
      (Profinite.padicAlgClCondensedRing l) (Profinite.PadicAlgCl.constSectionRingHom l)
      (fun _ _ ↦ rfl) a
  have hv (a : PadicAlgCl l) :
      ((Profinite.padicAlgClCondensedRing l).obj.ringHomΓCompForget₂
        (Profinite.PadicAlgCl.constSectionRingHom l) (fun _ _ ↦ rfl) a).hom.app
          (op (Profinite.of PUnit.{u + 1})) (ULift.up 1) =
        Profinite.PadicAlgCl.constSectionRingHom l (op (Profinite.of PUnit.{u + 1})) a :=
    (congrArg (· * Profinite.PadicAlgCl.constSectionRingHom l (op (Profinite.of PUnit.{u + 1})) a)
      (Int.cast_one (R := (Profinite.padicAlgClCondensedRing l).obj.obj
        (op (Profinite.of PUnit.{u + 1}))))).trans (one_mul _)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    hx, hx]
  refine (congrArg (ConcreteCategory.hom ((((upperStarFromPointAdj X).homEquiv _ _)
    (condensedRingObjIsoForgetAb l X).hom).hom.app (op (Profinite.of PUnit.{u + 1})))) (hv c)).trans
    ((upperStarFromPointAdj_homEquiv_condensedRingObjIsoForgetAb_hom_app X _ c).trans ?_)
  refine Eq.trans ?_ (congrArg (fun y ↦ ConcreteCategory.hom
    ((((toSpecZ X)_*[Ab] ⋙ pointLowerStar).map ((weilCoefficientsForgetAb l X).map
      (ULift.up.{u + 1} c • 𝟙 (adicConstantSheaf l X)))).hom.app (op (Profinite.of PUnit.{u + 1})))
    (ConcreteCategory.hom ((((upperStarFromPointAdj X).homEquiv _ _)
      (condensedRingObjIsoForgetAb l X).hom).hom.app (op (Profinite.of PUnit.{u + 1}))) y))
    (hv 1)).symm
  rw [upperStarFromPointAdj_homEquiv_condensedRingObjIsoForgetAb_hom_app]
  refine Eq.trans ?_ (AdicSheaf.smul_eq_constSection_mul (ULift.up.{u + 1} c)
    (AdicSheaf.constScalarSection (op ((profiniteToProEtOf X).obj (Profinite.of PUnit.{u + 1})))
      (ULift.up.{u + 1} (1 : PadicAlgCl l)))).symm
  exact congrArg ULift.up ((_root_.mul_one _).symm.trans (congrArg (_ * ·) (map_one _).symm))

/-- The underlying morphism of `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso` is
the inverse of the coefficient comparison `ℚ̲̄_ℓ,X ≅ forgetAb ℚ̄_ℓ,X`. -/
lemma adicSheafEquivCondensedModUnitIso_hom_hom (X : Scheme.{u}) :
    (adicSheafEquivCondensedModUnitIso l X).hom.hom = (condensedRingObjIsoForgetAb l X).inv := by
  refine (Category.id_comp _).trans ?_
  exact IsIso.inv_eq_of_hom_inv_id (condensedRingObjIsoForgetAb l X).hom_inv_id

/-- The underlying morphism of the inverse of
`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso` is the coefficient comparison
`ℚ̲̄_ℓ,X ≅ forgetAb ℚ̄_ℓ,X`. -/
lemma adicSheafEquivCondensedModUnitIso_inv_hom (X : Scheme.{u}) :
    (adicSheafEquivCondensedModUnitIso l X).inv.hom = (condensedRingObjIsoForgetAb l X).hom :=
  Category.comp_id _

/-- **The comparison of the two models is `ℚ̄_ℓ`-linear on the unit**: the equivalence
`AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}` sends the multiplication by `c ∈ ℚ̄_ℓ` on `ℚ̄_ℓ,X` to the
multiplication by the constant global section `c` on the regular module `ℚ̲̄_ℓ,X`. -/
lemma adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom (X : Scheme.{u})
    (c : PadicAlgCl l) :
    (adicSheafEquivCondensedModUnitIso l X).inv ≫
        (adicSheafEquivCondensedMod l X).functor.map
          (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit l X)) ≫
        (adicSheafEquivCondensedModUnitIso l X).hom =
      (Mod.regularEndRingHom (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
        (Profinite.PadicAlgCl.constRingHom l) X c)).asHom := by
  refine Mod.regular_hom_ext ?_
  rw [Mod.regularEndRingHom_apply, Mod.one_comp_regularLift_regular, Mod.comp_hom', Mod.comp_hom',
    adicSheafEquivCondensedModUnitIso_hom_hom, adicSheafEquivCondensedModUnitIso_inv_hom]
  have h1 : (MonObj.one : 𝟙_ _ ⟶ condensedRingObj (Profinite.padicAlgClRingObj l) X) =
      (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
        (Profinite.PadicAlgCl.constRingHom l) X 1).hom := by
    rw [map_one]
    rfl
  rw [h1]
  have h2 := congrArg (· ≫ (condensedRingObjIsoForgetAb l X).inv)
    (constRingHom_hom_comp_condensedRingObjIsoForgetAb_hom X c).symm
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
  exact h2

variable (l) in
/-- **The comparison of the two models is `ℚ̄_ℓ`-linear on the unit**, at a separably closed
point: through `End (𝟙_ Mod_{Spec Ω}) ≅ ℚ̄_ℓ`, the image of the multiplication by `c` on
`ℚ̄_ℓ,Spec Ω` is `c`. -/
theorem endTensorUnitRingEquiv_adicSheafEquivCondensedMod_map_smul (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (c : PadicAlgCl l) :
    CondensedRing.endTensorUnitRingEquiv l Ω
        (.of ((adicSheafEquivCondensedModUnitIso l (Spec (.of Ω))).inv ≫
          (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.map
            (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit l (Spec (.of Ω)))) ≫
          (adicSheafEquivCondensedModUnitIso l (Spec (.of Ω))).hom)) = c := by
  rw [adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom]
  refine Eq.trans ?_ (CondensedRing.endTensorUnitRingEquiv_scalarEndRingHom l Ω c)
  rw [CondensedRing.scalarEndRingHom_eq_map]
  exact congrArg (fun t ↦ CondensedRing.endTensorUnitRingEquiv l Ω (.of t))
    (Functor.mapMod_map_regularEndRingHom _ _ _).symm

end AlgebraicGeometry.ProEtale
