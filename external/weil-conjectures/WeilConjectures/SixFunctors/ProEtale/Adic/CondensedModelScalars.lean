/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# The constants in the two models of `ℓ`-adic sheaves

The constants `ℚ̄_ℓ` act on the two models of `ℓ`-adic sheaves on a scheme `X`: on the sheaves
of modules over `ℚ̄_ℓ,X` of the old model through the constant functions
(`AlgebraicGeometry.ProEtale.AdicSheaf.constScalarSection`), and on the module objects over
`Λ_X = p_X^* ℚ̲̄_ℓ` of the condensed model through the pullbacks `p_X^* c` of the constant global
sections of `ℚ̲̄_ℓ` (`AlgebraicGeometry.ProEtale.CondensedRing.constRingHom`). This file shows
that the comparison `Λ_X ≅ forgetAb ℚ̄_ℓ,X` of the coefficient rings
(`AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`) matches them
(`AlgebraicGeometry.ProEtale.unitHomEval_constRingHom_comp_condensedRingObjIsoForgetAb_hom`).

The proof evaluates on the test object `X[*]`: by adjunction, the global section `p_X^* c` of
`Λ_X`, followed by the realization `Λ_X ≅ ℚ̄_ℓ,X` of the coefficients as bounded functions,
is computed by the normalization of this realization on the profinite test functions
(`AlgebraicGeometry.ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso_test`),
applied to the constant function `c` on the point.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (T : Type*) [TopologicalSpace T]

/-- The constant functions `T → ℚ̄_ℓ`, with values in a finite subextension. -/
noncomputable def finiteIntermediateFieldValuedConst :
    PadicAlgCl ℓ →+* finiteIntermediateFieldValued ℓ T :=
  (ContinuousMap.C (α := T) (A := PadicAlgCl ℓ)).codRestrict
    (finiteIntermediateFieldValued ℓ T) fun a ↦
      ⟨IntermediateField.adjoin ℚ_[ℓ] {a},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a),
        fun _ ↦ IntermediateField.mem_adjoin_simple_self ℚ_[ℓ] a⟩

@[simp]
lemma finiteIntermediateFieldValuedConst_apply (a : PadicAlgCl ℓ) (t : T) :
    (finiteIntermediateFieldValuedConst ℓ T a).1 t = a :=
  rfl

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The value at the terminal object of the global section `p_X^* c` of `Λ_X`, realized as a
bounded function (`CondensedQbarCoefficientRealization.globalCoefficientIso`), is the constant
function `c`. -/
lemma unitHomEval_constRingHom_comp_globalCoefficientIso_hom (c : PadicAlgCl l) :
    Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        ((CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
          (Profinite.PadicAlgCl.constRingHom l) X c).hom ≫
          (CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom) =
      (toSheafify (ProEt.topology X) (CondensedQbarScalarConstruction.boundedP l X)).app
        (op (ProEt.mk (𝟙 X)))
        (ULift.up (PadicAlgCl.finiteIntermediateFieldValuedConst l X c)) := by
  obtain ⟨k, hk⟩ := Sheaf.unitHomEval_surjective (J := ProEt.topology X) (ProEt.isTerminalMkId X)
    (padicAlgClSheaf X l)
    ((toSheafify (ProEt.topology X) (CondensedQbarScalarConstruction.boundedP l X)).app
      (op (ProEt.mk (𝟙 X))) (ULift.up (PadicAlgCl.finiteIntermediateFieldValuedConst l X c)))
  rw [← hk, CondensedRing.constRingHom_hom, Category.assoc]
  have e : (CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom =
      ((upperStarFromPointAdjunction X).homEquiv _ _).symm
        ((upperStarFromPointAdjunction X).homEquiv _ _
          (CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [e, (upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq _ _ k ?_]
  refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{u})
    Profinite.isTerminalPUnit _ ?_
  refine (Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{u}) _ _ _).trans ?_
  rw [show Sheaf.unitHomEval (Profinite.of PUnit.{u + 1})
      (Profinite.PadicAlgCl.constRingHom l c).hom =
      Profinite.PadicAlgCl.constSectionRingHom l (op (Profinite.of PUnit.{u + 1})) c from
    Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u}) _
      (Profinite.padicAlgClCondensedRing l) _ (fun _ _ ↦ rfl) c]
  erw [CondensedQbarCoefficientRealization.globalCoefficientIso_test]
  have e₂ : ε ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar) ≫
      ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar).map k =
      ε pointLowerStar ≫ pointLowerStar.map (ε (toSpecZ X)_*[Ab.{u + 1}] ≫
        (toSpecZ X)_*[Ab.{u + 1}].map k) := by
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc, Functor.comp_map, ← Functor.map_comp]
  rw [e₂]
  unfold pointLowerStar
  refine Eq.trans ?_ (Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
    (J := coherentTopology Profinite.{u}) (K := ProEt.topology specZ.{u})
    (T := Profinite.of PUnit.{u + 1}) profiniteToProEt (ProEt.isTerminalMkId specZ)
    (ε (toSpecZ X)_*[Ab.{u + 1}] ≫ (toSpecZ X)_*[Ab.{u + 1}].map k)).symm
  erw [unitHomEval_ε_comp_lowerStar_map, hk]
  erw [← NatTrans.naturality_apply]
  refine Eq.trans ?_ (NatTrans.naturality_apply
    (toSheafify (ProEt.topology X) (CondensedQbarScalarConstruction.boundedP l X))
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).map
      ((ProEt.isTerminalMkId specZ).from (profiniteToProEt.obj (Profinite.of PUnit.{u + 1})))).op
    _)
  exact congrArg _ (ULift.ext (Subtype.ext (ContinuousMap.ext fun _ ↦ rfl)))

/-- The comparison `ℚ̄_ℓ,X ⟶ forgetAb ℚ̄_ℓ,X` of the two models of the constant sheaf is, on the
sections coming from bounded functions, the inclusion of the bounded functions into the locally
finite functions. -/
lemma padicAlgClSheafToAdicConstantSheaf_hom_app_toSheafify (U : X.ProEtᵒᵖ)
    (x : (CondensedQbarScalarConstruction.boundedP l X).obj U) :
    (padicAlgClSheafToAdicConstantSheaf X l).hom.app U
        ((toSheafify (ProEt.topology X) (CondensedQbarScalarConstruction.boundedP l X)).app U x) =
      (padicAlgClPresheafToAdicConstantSheaf X l).app U x :=
  congrArg (fun g ↦ g.app U x) (toSheafify_sheafifyLift (ProEt.topology X)
    (padicAlgClPresheafToAdicConstantSheaf X l)
    ((sheafCompose (ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
      (adicConstantSheaf l X)).property)

/-- **The constants in the two models of `ℓ`-adic sheaves**: the comparison `Λ_X ≅ forgetAb ℚ̄_ℓ,X`
of the coefficient rings sends the global section `p_X^* c` of `Λ_X` to the constant function
`c`. -/
theorem unitHomEval_constRingHom_comp_condensedRingObjIsoForgetAb_hom (c : PadicAlgCl l) :
    Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        ((CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
          (Profinite.PadicAlgCl.constRingHom l) X c).hom ≫
          (condensedRingObjIsoForgetAb l X).hom) =
      AdicSheaf.constScalarSection (op (ProEt.mk (𝟙 X))) (ULift.up c) := by
  have e : (condensedRingObjIsoForgetAb l X).hom =
      (CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf X l :=
    rfl
  rw [e, ← Category.assoc]
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).trans ?_
  erw [unitHomEval_constRingHom_comp_globalCoefficientIso_hom,
    padicAlgClSheafToAdicConstantSheaf_hom_app_toSheafify]
  rfl

namespace AdicSheaf

variable {l X}

/-- The action of a global section `σ` of `forgetAb ℚ̄_ℓ,X` on a module object `N` over it, on
the sections over `U`: the action of the value of `σ` over `U`. -/
lemma globalSmul_hom_app (σ : 𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶
      (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X))
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)))
    (U : X.ProEtᵒᵖ) (x : N.X.obj.obj U) :
    (Mod.globalSmul σ N).hom.app U x =
      abSectionAct N ((ε (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}) ≫ σ.hom).app U
        (ULift.up 1)) x := by
  have h : (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).map (Mod.globalSmul σ N) =
      (λ_ _).inv ≫ (ε (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}) ≫ σ.hom) ▷ _ ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
          ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X ≫
          (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).map (Mod.act N.X) := by
    rw [Mod.globalSmul, Functor.map_comp, Functor.map_comp,
      ← Functor.LaxMonoidal.left_unitality_inv, comp_whiskerRight, Category.assoc,
      Category.assoc, Category.assoc]
    congr 2
    exact (Functor.LaxMonoidal.μ_natural_left_assoc _ σ N.X _).symm
  exact congrArg (fun f ↦ f.app U x) h

end AdicSheaf

/-- **The constants act in the same way in the two models**: for an `ℓ`-adic sheaf `A` on `X`
and a global section `m` of the underlying abelian sheaf of the corresponding module object
`E A`, the action of the constant global section `p_X^* c` of `Λ_X` on `m` corresponds, on the
sections over `X`, to the scalar multiplication by `c` of the old model. -/
theorem unitHomEval_comp_globalSmul_constRingHom (A : AdicSheaf l X)
    (m : 𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶
      ((adicSheafEquivCondensedMod l X).functor.obj A).X) (c : PadicAlgCl l) :
    Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        (m ≫ Mod.globalSmul (CondensedRing.constRingHom (Profinite.padicAlgClRingObj l)
          (Profinite.PadicAlgCl.constRingHom l) X c).hom
          ((adicSheafEquivCondensedMod l X).functor.obj A)) =
      (ULift.up c : ULift.{u + 1} (PadicAlgCl l)) •
        @id (A.X.obj.obj (op (ProEt.mk (𝟙 X))))
          (Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X)) m) := by
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).trans ?_
  erw [Mod.globalSmul_comap, AdicSheaf.globalSmul_hom_app]
  exact (congrArg (fun a ↦ AdicSheaf.abSectionAct _ a _)
    (unitHomEval_constRingHom_comp_condensedRingObjIsoForgetAb_hom l X c)).trans
    (AdicSheaf.abSectionAct_forgetAb_obj_constSection A _ _)

end AlgebraicGeometry.ProEtale
