/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

/-!

# The integral point fibre functor modulo `ℓⁿ`

Over the separably closed point `s = Spec k`, the integral point fibre functor
`Fib_s : Dᵇc(s)⟦𝒪̲_E⟧ ⥤ D(𝒪_E)` (`ProEtale.CondensedRing.pointFiberFunctorIntegral`) and the
reduction modulo `ℓⁿ` read on the étale site (`ProEtale.CondensedRing.etaleReduction`) are
related by the reduction triangle: for every `N`, there is a distinguished triangle
```
Fib_s(N) --ℓⁿ--> Fib_s(N) --π--> RΓ(s, N ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⟶ Fib_s(N)[1]
```
in `D(𝒪_E)`, the last object read through restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
with `π` natural in `N` (`ProEtale.CondensedRing.exists_pointFiberFunctorIntegral_reduction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ) (n : ℕ)

/-- The reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, between the universe-lifted coefficient rings of the
integral point fibre functor and of the étale reduction. -/
noncomputable def integersModPowCoeffHom :
    Shrink.{u + 1} (integers ℓ E.1) →+* integersModPowCoeff.{u} ℓ E.1 n :=
  (ULift.ringEquiv.symm.toRingHom).comp
    ((integersModPowMk ℓ E.1 n).comp (Shrink.ringEquiv _).toRingHom)

/-! ### Sections over the point of `𝒪_E ⧸ ℓⁿ`-modules -/

/-- The abelian category of `(𝒪_E ⧸ ℓⁿ)̲`-module objects on the pro-étale site of the point
`s = Spec k`. -/
abbrev PointModIntegersModPow : Type _ :=
  Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj (Profinite.integersModPowRingObj.{u} ℓ E.1 n) (point k).left)

/-- The terminal object `s` of the pro-étale site of the point `s = Spec k`. -/
noncomputable abbrev pointProEtTerminal : (point k).left.ProEt :=
  Scheme.ProEt.mk (𝟙 (point k).left)

/-- The identification of `(𝒪_E ⧸ ℓⁿ)̲`-module objects on `s_proét` with pro-étale sheaves of
`𝒪_E ⧸ ℓⁿ`-modules (`ProEtale.finiteCoefficientModEquivalence`). -/
noncomputable abbrev pointModIntegersModPowEquivalence :=
  finiteCoefficientModEquivalence (point k).left (PadicAlgCl.integersModPow ℓ E.1 n)

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` sends the constant global section `r` to the constant
global section `r mod ℓⁿ`. -/
lemma Γ_map_padicIntegersConstRingHom_reduction (r : PadicAlgCl.integers ℓ E.1) :
    MonObj.Γ.map (Profinite.padicIntegersRingObjToIntegersModPow.{u} ℓ E.1 n)
        (padicIntegersConstRingHom ℓ E r) =
      Profinite.continuousMapConstRingHom (PadicAlgCl.integersModPow ℓ E.1 n)
        (PadicAlgCl.integersModPowMk ℓ E.1 n r) :=
  Sheaf.Γ_map_ringHomΓSheafCompose _ (Profinite.padicIntegersCondensedRingToIntegersModPow ℓ E.1 n)
    _ (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl) fun _ ↦ rfl

/-- The sections over the point of the restriction of scalars of a `(𝒪_E ⧸ ℓⁿ)̲`-module `M`, as an
abelian group: `Hom(𝒪̲_E, M) = Hom(𝟙, M) = M(s)`. -/
noncomputable def pointSectionsComapAddEquiv (M : PointModIntegersModPow ℓ k E n) :
    (pointSectionsIntegral ℓ k E).obj
        ((Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).obj M) ≃+
      M.X.obj.obj (op (pointProEtTerminal k)) :=
  (Mod.regularHomAddEquiv _).trans
    (Sheaf.unitHomEvalAddEquiv (J := Scheme.ProEt.topology (point k).left)
      (Scheme.ProEt.isTerminalMkId (point k).left) M.X)

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The sections over the point of a morphism `𝒪̲_E ⟶ M` are its value at the unit section. -/
lemma pointSectionsComapAddEquiv_apply (M : PointModIntegersModPow ℓ k E n)
    (x : 𝟙_ (PointModIntegral ℓ k E) ⟶
      (Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).obj M) :
    pointSectionsComapAddEquiv ℓ k E n M x =
      Sheaf.unitHomEval (J := Scheme.ProEt.topology (point k).left) (pointProEtTerminal k)
        (η[condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left] ≫ x.hom) :=
  rfl

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The action of `a ∈ 𝒪_E` on the sections over the point, unfolded. -/
lemma pointSectionsComapAddEquiv_smul_eq (M : PointModIntegersModPow ℓ k E n)
    (a : Shrink.{u + 1} (integers ℓ E.1))
    (x : (pointSectionsIntegral ℓ k E).obj
        ((Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).obj M)) :
    pointSectionsComapAddEquiv ℓ k E n M (a • x) =
      Sheaf.unitHomEval (J := Scheme.ProEt.topology (point k).left) (pointProEtTerminal k)
        (η[condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left] ≫
          (Mod.regularLift _ (MonObj.Γ.mapFunctor (upperStarFromPoint (point k).left)
            (padicIntegersConstRingHom ℓ E ((shrinkRingEquiv ℓ E.1).symm a))).hom ≫ x).hom) :=
  rfl

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The scalar `a ∈ 𝒪_E` acts on the sections over the point of the restriction of scalars of a
`(𝒪_E ⧸ ℓⁿ)̲`-module `M` as the constant global section `a mod ℓⁿ` acts on `M`. -/
lemma pointSectionsComapAddEquiv_smul (M : PointModIntegersModPow ℓ k E n)
    (a : Shrink.{u + 1} (integers ℓ E.1))
    (x : (pointSectionsIntegral ℓ k E).obj
        ((Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).obj M)) :
    pointSectionsComapAddEquiv ℓ k E n M (a • x) =
      (Mod.globalSmul (ε (upperStarFromPoint (point k).left) ≫
        (upperStarFromPoint (point k).left).map
          (Profinite.continuousMapConstRingHom (PadicAlgCl.integersModPow ℓ E.1 n)
            (PadicAlgCl.integersModPowMk ℓ E.1 n ((shrinkRingEquiv ℓ E.1).symm a))).hom) M).hom.app
        (op (pointProEtTerminal k)) (pointSectionsComapAddEquiv ℓ k E n M x) := by
  let red := integersModPowReduction (point k).left ℓ E.1 n
  let p := upperStarFromPoint (point k).left
  let η₀ := η[condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left]
  let r := (shrinkRingEquiv ℓ E.1).symm a
  let σ := MonObj.Γ.mapFunctor p (padicIntegersConstRingHom ℓ E r)
  let τ := Profinite.continuousMapConstRingHom (PadicAlgCl.integersModPow ℓ E.1 n)
    (PadicAlgCl.integersModPowMk ℓ E.1 n r)
  have h : σ.hom ≫ red = ε p ≫ p.map τ.hom := by
    rw [MonObj.Γ.mapFunctor_hom, Category.assoc, ← Functor.map_comp, ← MonObj.Γ.map_hom,
      Γ_map_padicIntegersConstRingHom_reduction]
  have h₂ : Mod.globalSmul σ.hom ((Mod.comap red).obj M) =
      Mod.globalSmul (ε p ≫ p.map τ.hom) M := by
    rw [Mod.globalSmul_comap, h]
  let x' : Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left) ⟶
      (Mod.comap red).obj M := x
  rw [pointSectionsComapAddEquiv_smul_eq]
  refine (congrArg (Sheaf.unitHomEval (J := Scheme.ProEt.topology (point k).left)
    (pointProEtTerminal k)) (Mod.one_comp_regularLift_comp_hom σ.hom x')).trans ?_
  refine (Sheaf.unitHomEval_comp (J := Scheme.ProEt.topology (point k).left)
    (pointProEtTerminal k) (η₀ ≫ x'.hom) (Mod.globalSmul σ.hom ((Mod.comap red).obj M))).trans ?_
  exact congrArg (fun g : M.X ⟶ M.X ↦ (g.hom.app (op (pointProEtTerminal k))).hom
    (Sheaf.unitHomEval (J := Scheme.ProEt.topology (point k).left) (pointProEtTerminal k)
      (η₀ ≫ x'.hom))) h₂

/-- The sections over the point of the restriction of scalars of a `(𝒪_E ⧸ ℓⁿ)̲`-module `M` are
the sections over the point of the corresponding sheaf of `𝒪_E ⧸ ℓⁿ`-modules, as `𝒪_E`-modules. -/
noncomputable def pointSectionsComapLinearEquiv (M : PointModIntegersModPow ℓ k E n) :
    (pointSectionsIntegral ℓ k E).obj
        ((Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).obj M) ≃ₗ[Shrink.{u + 1}
          (integers ℓ E.1)]
      (ModuleCat.restrictScalars (integersModPowCoeffHom ℓ E n)).obj
        (((pointModIntegersModPowEquivalence ℓ k E n).functor.obj M).obj.obj
          (op (pointProEtTerminal k))) :=
  AddEquiv.toLinearEquiv (pointSectionsComapAddEquiv ℓ k E n M) fun a x ↦
    (pointSectionsComapAddEquiv_smul ℓ k E n M a x).trans
      (finiteCoefficientModEquivalence_smul _ _ M _ _ _).symm

/-- **Sections over the point of `𝒪_E ⧸ ℓⁿ`-modules**: for `(𝒪_E ⧸ ℓⁿ)̲`-module objects `M` on the
point, `Γ(s, M)` read as an `𝒪̲_E`-module is the sections over `s` of the corresponding sheaf of
`𝒪_E ⧸ ℓⁿ`-modules, read as an `𝒪_E`-module, naturally in `M`. -/
noncomputable def pointSectionsComapIso :
    Mod.comap (integersModPowReduction (point k).left ℓ E.1 n) ⋙ pointSectionsIntegral ℓ k E ≅
      (pointModIntegersModPowEquivalence ℓ k E n).functor ⋙
        (sheafSections (Scheme.ProEt.topology (point k).left)
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))).obj (op (pointProEtTerminal k)) ⋙
          ModuleCat.restrictScalars (integersModPowCoeffHom ℓ E n) :=
  NatIso.ofComponents (fun M ↦ (pointSectionsComapLinearEquiv ℓ k E n M).toModuleIso)
    fun {M M'} g ↦ by
      ext x
      let x' : Mod.regular
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left) ⟶
          (Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).obj M := x
      refine (congrArg (Sheaf.unitHomEval (J := Scheme.ProEt.topology (point k).left)
        (pointProEtTerminal k)) (Category.assoc
          (η[condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left])
          x'.hom g.hom).symm).trans ?_
      exact Sheaf.unitHomEval_comp (J := Scheme.ProEt.topology (point k).left)
        (pointProEtTerminal k)
        (η[condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left] ≫ x'.hom) g.hom

/-- The sections over the point of pro-étale sheaves of `𝒪_E ⧸ ℓⁿ`-modules are left exact, being
right adjoint to the constant sheaf functor. -/
instance preservesFiniteLimits_sheafSections_point :
    PreservesFiniteLimits ((sheafSections (Scheme.ProEt.topology (point k).left)
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))).obj (op (pointProEtTerminal k))) :=
  have := (constantSheafAdj (Scheme.ProEt.topology (point k).left)
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
    (Scheme.ProEt.isTerminalMkId (point k).left)).rightAdjoint_preservesLimits
  inferInstance

/-- The sections over the point of pro-étale sheaves of `𝒪_E ⧸ ℓⁿ`-modules are additive. -/
instance additive_sheafSections_point :
    ((sheafSections (Scheme.ProEt.topology (point k).left)
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))).obj
        (op (pointProEtTerminal k))).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- For `k` separably closed, the sections over the point of pro-étale sheaves of
`𝒪_E ⧸ ℓⁿ`-modules are right exact: read as `𝒪_E`-modules they are the sections
`Hom(𝒪̲_E, -)` of module objects (`pointSectionsComapIso`), which are exact since `𝒪̲_E` is
projective over the separably closed point. -/
instance preservesFiniteColimits_sheafSections_point :
    PreservesFiniteColimits ((sheafSections (Scheme.ProEt.topology (point k).left)
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))).obj (op (pointProEtTerminal k))) := by
  let Φ := pointModIntegersModPowEquivalence ℓ k E n
  let ev := (sheafSections (Scheme.ProEt.topology (point k).left)
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))).obj (op (pointProEtTerminal k))
  let rs := ModuleCat.restrictScalars.{u + 1} (integersModPowCoeffHom ℓ E n)
  have : PreservesFiniteColimits (Φ.functor ⋙ ev ⋙ rs) :=
    preservesFiniteColimits_of_natIso (pointSectionsComapIso ℓ k E n)
  have : PreservesFiniteColimits (ev ⋙ rs) :=
    preservesFiniteColimits_of_natIso ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight Φ.counitIso (ev ⋙ rs) ≪≫ (ev ⋙ rs).leftUnitor)
  have : ReflectsFiniteColimits rs :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves ev rs

/-- For `k` separably closed, the global sections over the point of pro-étale sheaves of
`𝒪_E ⧸ ℓⁿ`-modules are right exact. -/
instance preservesFiniteColimits_Γ_point :
    PreservesFiniteColimits (Sheaf.Γ (Scheme.ProEt.topology (point k).left)
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))) :=
  preservesFiniteColimits_of_natIso
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId (point k).left)).symm

/-- **Derived sections over the point of `𝒪_E ⧸ ℓⁿ`-modules**: on `D(Mod_{(𝒪_E ⧸ ℓⁿ)̲,s})`, the
integral derived sections `RΓ(s, -)` of the restriction of scalars to `𝒪̲_E` are the derived étale
sections `RΓ(s_ét, Rν_* -)` of the corresponding complex of pro-étale sheaves of
`𝒪_E ⧸ ℓⁿ`-modules, read as `𝒪_E`-modules. Both sections functors over the separably closed
point being exact, this is induced by `pointSectionsComapIso`, together with
`RΓ(s_ét, Rν_* -) ≅ RΓ(s_proét, -)`. -/
noncomputable def pointDerivedSectionsComapIso :
    (Mod.comap (integersModPowReduction (point k).left ℓ E.1 n)).mapDerivedCategory ⋙
        (pointSectionsIntegral ℓ k E).mapDerivedCategory ≅
      (pointModIntegersModPowEquivalence ℓ k E n).functor.mapDerivedCategory ⋙
        R(ν_*((point k).left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)]) ⋙
          Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
            (point k).left ⋙
          (ModuleCat.restrictScalars (integersModPowCoeffHom ℓ E n)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (pointSectionsComapIso ℓ k E n) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
            (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId (point k).left)).symm ≪≫
          (Sheaf.Γ (Scheme.ProEt.topology (point k).left)
            (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
            ).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
          (comparisonLowerStarCompRightDerivedGlobalSectionsIso _ (point k).left).symm) _ ≪≫
      Functor.associator _ _ _)

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The reduction triangle over the point, with the unit of the derived adjunction. -/
lemma exists_distinguished_pointReduction (K : DerivedCategory (PointModIntegral ℓ k E)) :
    ∃ h, Pretriangulated.Triangle.mk (((ℓ : ℤ) ^ n) • 𝟙 K)
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction (point k).left ℓ E.1 n)).unit.app K) h ∈ distTriang _ :=
  Mod.exists_distinguished_zsmul_derivedExtendMapDerivedCategoryUnit _ _
    (zsmul_id_comp_integersModPowReduction (point k).left ℓ E.1 n)
    (shortExact_integersModPowReduction (point k).left ℓ E.1 n) K

/-- The derived sections over the point of `𝒪_E ⧸ ℓⁿ`-module complexes, read on the étale site:
`RΓ(s_ét, Rν_* -)` read as `𝒪_E`-modules. -/
noncomputable abbrev pointEtaleSectionsRestrict :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (point k).left)
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (integers ℓ E.1))) :=
  R(ν_*((point k).left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)]) ⋙
    Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
      (point k).left ⋙
    (ModuleCat.restrictScalars (integersModPowCoeffHom ℓ E n)).mapDerivedCategory

/-- The natural transformation `π : Fib_s ⟶ RΓ(s_ét, (-) ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`: the image under `Fib_s` of
the unit `N ⟶ N ⊗ᴸ 𝒪_E ⧸ ℓⁿ` of the derived adjunction, followed by the identification
`pointDerivedSectionsComapIso` of the sections. -/
noncomputable def pointFiberReductionNatTrans :
    pointFiberFunctorIntegral ℓ k E ⟶
      etaleReduction ℓ E.1 n (point k) ⋙
        Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
          (point k).left ⋙
        (ModuleCat.restrictScalars (integersModPowCoeffHom ℓ E n)).mapDerivedCategory :=
  Functor.whiskerLeft (boundedConstructible _).ι
      (Functor.whiskerRight (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction (point k).left ℓ E.1 n)).unit
        (pointSectionsIntegral ℓ k E).mapDerivedCategory) ≫
    Functor.whiskerLeft ((boundedConstructible _).ι ⋙
        (Mod.extendScalars (integersModPowReduction (point k).left ℓ E.1 n)).leftDerivedFunctor)
      (pointDerivedSectionsComapIso ℓ k E n).hom ≫
    Functor.whiskerRight
      (boundedConstructibleIntegersModPowReductionCompatibility (point k).left ℓ E.1 n).inv
      ((pointModIntegersModPowEquivalence ℓ k E n).functor.mapDerivedCategory ⋙
        pointEtaleSectionsRestrict ℓ k E n)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The components of `pointFiberReductionNatTrans`. -/
lemma pointFiberReductionNatTrans_app
    (N : Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (pointFiberReductionNatTrans ℓ k E n).app N =
      (pointSectionsIntegral ℓ k E).mapDerivedCategory.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (integersModPowReduction (point k).left ℓ E.1 n)).unit.app N.obj) ≫
        (pointDerivedSectionsComapIso ℓ k E n).hom.app
          ((Mod.extendScalars
            (integersModPowReduction (point k).left ℓ E.1 n)).leftDerivedFunctor.obj
          N.obj) ≫
        ((pointModIntegersModPowEquivalence ℓ k E n).functor.mapDerivedCategory ⋙
          pointEtaleSectionsRestrict ℓ k E n).map
          ((boundedConstructibleIntegersModPowReductionCompatibility (point k).left ℓ E.1 n).inv.app
            N) :=
  rfl

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The integral derived sections over the point send the multiplication by an integer to the
multiplication by this integer. -/
lemma pointSectionsIntegral_mapDerivedCategory_map_zsmul_id (m : ℤ)
    (K : DerivedCategory (PointModIntegral ℓ k E)) :
    (pointSectionsIntegral ℓ k E).mapDerivedCategory.map (m • 𝟙 K) =
      m • 𝟙 ((pointSectionsIntegral ℓ k E).mapDerivedCategory.obj K) :=
  ((pointSectionsIntegral ℓ k E).mapDerivedCategory.map_zsmul (f := 𝟙 K) (r := m)).trans
    (congrArg (m • ·) ((pointSectionsIntegral ℓ k E).mapDerivedCategory.map_id K))

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **The integral point fibre functor modulo `ℓⁿ`**: there is a natural transformation
`π : Fib_s ⟶ RΓ(s, (-) ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` (read in `D(𝒪_E)`) such that for every `N` the triangle
`Fib_s(N) --ℓⁿ--> Fib_s(N) --π--> RΓ(s, N ⊗ᴸ 𝒪_E ⧸ ℓⁿ) ⟶` is distinguished. -/
theorem exists_pointFiberFunctorIntegral_reduction :
    ∃ π : pointFiberFunctorIntegral ℓ k E ⟶
        etaleReduction ℓ E.1 n (point k) ⋙
          Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n))
            (point k).left ⋙
          (ModuleCat.restrictScalars (integersModPowCoeffHom.{u} ℓ E n)).mapDerivedCategory,
      ∀ N, ∃ δ, Pretriangulated.Triangle.mk
        (((ℓ : ℤ) ^ n) • 𝟙 ((pointFiberFunctorIntegral ℓ k E).obj N))
        (π.app N) δ ∈ distTriang _ := by
  refine ⟨pointFiberReductionNatTrans ℓ k E n, fun N ↦ ?_⟩
  refine (exists_distinguished_pointReduction ℓ k E n N.obj).elim fun h hT ↦ ?_
  refine Pretriangulated.exists_distinguished_of_isos _
    ((pointSectionsIntegral ℓ k E).mapDerivedCategory.map_distinguished _ hT) _ _
    (Iso.refl _) (Iso.refl _)
    ((pointDerivedSectionsComapIso ℓ k E n).app _ ≪≫
      ((pointModIntegersModPowEquivalence ℓ k E n).functor.mapDerivedCategory ⋙
        pointEtaleSectionsRestrict ℓ k E n).mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility (point k).left ℓ E.1 n).app
          N).symm) ?_ ?_
  · exact (Category.comp_id _).trans ((pointSectionsIntegral_mapDerivedCategory_map_zsmul_id
      ℓ k E _ N.obj).trans (Category.id_comp _).symm)
  · exact (pointFiberReductionNatTrans_app ℓ k E n N).symm.trans (Category.id_comp _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
