/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalarsQuotient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafEquivalenceLift

/-!
# Change of finite coefficient rings in the two models of finite coefficients

Let `ρ : T →+* T'` be a homomorphism of finite discrete commutative rings and `X` a scheme. The
identifications `ProEtale.finiteCoefficientModEquivalence` of module objects over
`Λ_X = p_X^* T̲` with pro-étale sheaves of `T`-modules are compatible with the change of rings
along `ρ`:

* restriction of scalars along the morphism of coefficient rings `T_X ⟶ T'_X` induced by `ρ`
  corresponds to restriction of scalars of sheaves of modules
  (`ProEtale.finiteCoefficientModEquivalenceComapIso`), and so do the induced functors on derived
  categories (`ProEtale.finiteCoefficientDerivedEquivalenceComapIso`);
* if `ρ` is surjective with principal kernel, the derived extension of scalars of module objects
  corresponds to the derived extension of scalars of sheaves of modules
  (`ProEtale.finiteCoefficientDerivedEquivalenceExtendScalarsIso`), both being left adjoint to the
  restrictions of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
  [DiscreteTopology T'] [Finite T'] (ρ : T →+* T')

/-- The multiplication by a scalar `c` on the sheaf of `T`-modules corresponding to the restriction
of scalars of a module object `M` over `T'_X` is the multiplication by `ρ c` on the sheaf of
`T'`-modules corresponding to `M`: both are the actions on `M` of the constant global section
`ρ c`. -/
lemma sheafCompose_map_smulEnd_comap
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T') X)) (c : ULift.{u + 1} T) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T))
        Ab.{u + 1})).map (Sheaf.smulEnd ((finiteCoefficientModEquivalence X T).functor.obj
          ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
            continuous_of_discreteTopology) X)).obj M)) c) =
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T))
        Ab.{u + 1})).map (Sheaf.smulEnd ((Sheaf.restrictScalars (Scheme.ProEt.topology X)
          ρ.ulift).obj ((finiteCoefficientModEquivalence X T').functor.obj M)) c) := by
  ext U y
  refine (finiteCoefficientModEquivalence_smul X T _ U c.down y).trans ?_
  refine Eq.trans ?_ (finiteCoefficientModEquivalence_smul X T' M U (ρ c.down) y).symm
  rw [Mod.globalSmul_comap, Category.assoc, ← Functor.map_comp,
    Profinite.continuousMapConstRingHom_hom_comp_continuousMapRingObjMap]
  rfl

/-- **Restriction of scalars in the two models of finite coefficients**: under the
identifications `finiteCoefficientModEquivalence`, restriction of scalars of module objects
along the morphism `T_X ⟶ T'_X` induced by `ρ : T →+* T'` is restriction of scalars of pro-étale
sheaves of modules along `ρ`. Both keep the underlying abelian sheaves, and the scalars act
through the constant global sections (`finiteCoefficientModEquivalence_smul`). -/
noncomputable def finiteCoefficientModEquivalenceComapIso :
    Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
        continuous_of_discreteTopology) X) ⋙ (finiteCoefficientModEquivalence X T).functor ≅
      (finiteCoefficientModEquivalence X T').functor ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X) ρ.ulift :=
  Sheaf.isoOfSheafComposeForget₂
    (P := Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
      continuous_of_discreteTopology) X) ⋙ (finiteCoefficientModEquivalence X T).functor)
    (Q := (finiteCoefficientModEquivalence X T').functor ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology X) ρ.ulift)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl) fun M c ↦
    (Category.comp_id _).trans ((sheafCompose_map_smulEnd_comap X ρ M c).trans
      (Category.id_comp _).symm)

/-- **Restriction of scalars in the two derived models of finite coefficients**: the derived
form of `finiteCoefficientModEquivalenceComapIso`. -/
noncomputable def finiteCoefficientDerivedEquivalenceComapIso :
    (Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
        continuous_of_discreteTopology) X)).mapDerivedCategory ⋙
        (finiteCoefficientDerivedEquivalence X T).functor ≅
      (finiteCoefficientDerivedEquivalence X T').functor ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ.ulift :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (finiteCoefficientModEquivalenceComapIso X ρ) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

variable {ρ} (hρ : Function.Surjective ρ) {a : ULift.{u + 1} T}
  (ha : RingHom.ker ρ.ulift = Ideal.span {a})

/-- **Extension of scalars in the two derived models of finite coefficients**: for a surjective
`ρ : T →+* T'` with principal kernel, under the identifications
`finiteCoefficientDerivedEquivalence`, the derived extension of scalars of pro-étale sheaves of
modules along `ρ` corresponds to the derived extension of scalars of module objects along
`T_X ⟶ T'_X`: both are left adjoint to the restrictions of scalars, which correspond to each
other (`finiteCoefficientDerivedEquivalenceComapIso`). -/
noncomputable def finiteCoefficientDerivedEquivalenceExtendScalarsIso :
    (finiteCoefficientDerivedEquivalence X T).functor ⋙
        derivedExtendScalars (φ := ρ.ulift) (fun y ↦ ⟨⟨(hρ y.down).choose⟩,
          ULift.ext (hρ y.down).choose_spec⟩) ha X ≅
      (Mod.extendScalars (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) X)).leftDerivedFunctor ⋙
        (finiteCoefficientDerivedEquivalence X T').functor :=
  let Φ := finiteCoefficientDerivedEquivalence X T
  let Φ' := finiteCoefficientDerivedEquivalence X T'
  let ψ := coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ continuous_of_discreteTopology) X
  let i := finiteCoefficientDerivedEquivalenceComapIso X ρ
  let i' : (Φ'.inverse ⋙ (Mod.comap ψ).mapDerivedCategory) ⋙ Φ.functor ≅
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ.ulift :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Φ'.inverse i ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight Φ'.counitIso _ ≪≫
      Functor.leftUnitor _
  (conjugateIsoEquiv ((Mod.derivedExtendMapDerivedCategoryAdjunction ψ).comp Φ'.toAdjunction)
    (Φ.toAdjunction.comp (derivedExtendScalarsAdjunction _ ha X))).symm
    (Iso.isoCompInverse i')

end AlgebraicGeometry.ProEtale
