/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport

/-!
# The constant sections of `𝔽_{E,X}`

The constant global sections of the coefficient ring object `T_X = p_X^* T̲` of a Hausdorff totally
disconnected topological ring `T`, given by constant continuous maps `X → T`, are the images under
`p_X^*` of the constant global sections of the condensed ring `T̲`
(`ProEtale.continuousMapCoefficientSectionRingHom_const_hom`). In particular
`ProEtale.ResidueFieldSectionFac X ℓ E` holds for every scheme `X`
(`ProEtale.residueFieldSectionFac`), so that `ProEtale.residueFieldModuleSheaf X ℓ E` is an
equivalence of categories.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

section Const

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [T2Space T] [TotallyDisconnectedSpace T]

omit [T2Space T] [TotallyDisconnectedSpace T] in
/-- The constant global section `t` of `T̲`, followed by `T̲ ⟶ p_{X*} C(-, T)_X`, is the image
under `p_{X*}` of the global section of `C(-, T)_X` given by the constant map `t`. -/
lemma continuousMapConstRingHom_hom_comp_continuousMapToLowerStar (t : T) :
    (Profinite.continuousMapConstRingHom.{u} T t).hom ≫ continuousMapToLowerStar X T =
      ε ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar) ≫
        ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar).map
          (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom := by
  refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{u})
    Profinite.isTerminalPUnit _ ?_
  refine (Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{u}) _ _ _).trans ?_
  rw [show Sheaf.unitHomEval (Profinite.of PUnit.{u + 1})
      (Profinite.continuousMapConstRingHom.{u} T t).hom =
      Profinite.continuousMapConstSectionRingHom T (op (Profinite.of PUnit.{u + 1})) t from
    Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u}) _
      (Profinite.continuousMapRingSheaf T) _ (fun _ _ ↦ rfl) t]
  have e : ε ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar) ≫
      ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar).map
        (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom =
      ε pointLowerStar ≫ pointLowerStar.map (ε (toSpecZ X)_*[Ab.{u + 1}] ≫
        (toSpecZ X)_*[Ab.{u + 1}].map
          (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom) := by
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc, Functor.comp_map, ← Functor.map_comp]
  rw [e]
  unfold pointLowerStar
  refine Eq.trans ?_ (Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
    (J := coherentTopology Profinite.{u}) (K := ProEt.topology specZ.{u})
    (T := Profinite.of PUnit.{u + 1}) profiniteToProEt (ProEt.isTerminalMkId specZ)
    (ε (toSpecZ X)_*[Ab.{u + 1}] ≫ (toSpecZ X)_*[Ab.{u + 1}].map
      (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom)).symm
  erw [unitHomEval_ε_comp_lowerStar_map, unitHomEval_continuousMapSectionRingHom]
  refine ULift.ext (ContinuousMap.ext fun x ↦ rfl)

/-- **The constant global sections of `T_X` are pulled back from `T̲`**: the global section of
`T_X = p_X^* T̲` given by the constant map `t : X → T` is the image under `p_X^*` of the constant
global section `t` of the condensed ring `T̲`. -/
lemma continuousMapCoefficientSectionRingHom_const_hom (t : T) :
    (continuousMapCoefficientSectionRingHom X T (ContinuousMap.const X t)).hom =
      ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom := by
  rw [continuousMapCoefficientSectionRingHom_hom,
    ← (upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq _ _ _
      (continuousMapConstRingHom_hom_comp_continuousMapToLowerStar X T t)]
  change (_ ≫ _ ≫ continuousMapComparison X T) ≫ _ = _
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Const

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The constant global sections of `𝔽_{E,X}` are the images under `p_X^*` of the constant global
sections of `𝔽̲_E`. -/
theorem residueFieldSectionFac : ResidueFieldSectionFac X ℓ E := fun c ↦ by
  have h : (algebraMap (integersResidueField ℓ E) C(X, integersResidueField ℓ E))
      (ULift.down c) = ContinuousMap.const X (ULift.down c) :=
    ContinuousMap.ext fun _ ↦ by simp
  refine Eq.trans ?_ (continuousMapCoefficientSectionRingHom_const_hom X _ (ULift.down c))
  exact congrArg (fun f ↦ (continuousMapCoefficientSectionRingHom X _ f).hom) h

/-- **`residueFieldModuleSheaf X ℓ E` is an equivalence of categories** between module objects
over `𝔽_{E,X}` and pro-étale sheaves of `𝔽_E`-modules. -/
instance isEquivalence_residueFieldModuleSheaf : (residueFieldModuleSheaf X ℓ E).IsEquivalence :=
  isEquivalence_residueFieldModuleSheaf_of_section X ℓ E (residueFieldSectionFac X ℓ E)

end AlgebraicGeometry.ProEtale
