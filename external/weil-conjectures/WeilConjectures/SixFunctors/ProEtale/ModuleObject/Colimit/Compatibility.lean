/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.Algebra.Module.FiniteDimension
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextensionBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushFiniteFree

/-!

# Compatibility of the six functors with the extension of `ℓ`-adic coefficients

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ_ℓ` inside `ℚ̄_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) and `Ω = ℚ̄_ℓ`. The inclusions of condensed rings
`E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`) and `E̲ ⟶ ℚ̲̄_ℓ`
(`Profinite.padicSubfieldRingObjToPadicAlgCl`) of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` pull back, on a
scheme `X`, to coefficient changes `ι : E_X ⟶ F_X` and `ι : E_X ⟶ ℚ̄_ℓ,X`
(`ProEtale.coefficientMap`), inducing the derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - .
```
The comparisons (Pull), (Push) and (Shriek) between these and the derived functors `Lf^*`,
`Rf_*`, `Rf_!` on module objects are the ones of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, for these two
coefficient changes. This file supplies the coefficient-specific input:

* `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`), the pullback along the
  left adjoint `p_X^*` of `ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`);
* both coefficient changes are flat, so that (Pull) and (Push) are defined on the unbounded
  derived categories, and (Pull) is an isomorphism there
  (`ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`,
  `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`).
  On the point, `F̲` and `ℚ̲̄_ℓ` are copowers of the regular `E̲`-module: an `E`-basis of `F`,
  resp. of `ℚ̄_ℓ`, decomposes the presheaves `C(-, F)`, resp. `C(-, ℚ̄_ℓ)` with locally finite
  values, sectionwise (the coordinates are continuous, being `ℚ_ℓ`-linear maps on finite
  dimensional spaces), and sheafification preserves the decomposition. The monoidal left adjoint
  `p_X^*` carries it to `X`, and a copower of the unit is flat;
* for a finite extension `F/E`, (Push) is an isomorphism on all unbounded objects, hence so is
  (Shriek) (`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`): an `E`-basis
  of `F` is a basis of `F̲` over `E̲` made of constant global sections
  (`Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`), so this is the
  case of a finite free coefficient change
  (`ProEtale.CondensedRing.isIso_derivedPushHom_of_isIso_biproductDesc_globalSmul`);
* for `E ⊆ Ω`, (Push) is an isomorphism at bounded below objects for every quasi-compact
  quasi-separated `f`, by the continuity of `Rf_*` on bounded below complexes
  (`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`,
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite`), hence so is
  (Shriek) (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom_app_padicAlgCl_of_isGE`). It is
  not an isomorphism on all unbounded objects, even for proper `f`: `Rf_*` need not commute
  with direct sums (blueprint `sk-rem-sf-fullcd-scope`), while `ℚ̄_ℓ ≅ ⨁_ℕ E` as `E`-modules.

-/

@[expose] public section

universe u v

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### Copower decompositions of restricted regular modules -/

namespace CategoryTheory.Mod

open MonoidalCategory MonObj

section MapCopower

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]

private noncomputable def mapRestrictedRegularIso :
    (F.mapMod R).obj ((comap a).obj (regular S)) ≅
      (comap (F.map a)).obj (regular (F.obj S)) :=
  (F.mapModComapIso a).app (regular S) ≪≫
    (comap (F.map a)).mapIso (F.mapModRegularIso S)

/-- A functor preserving coproducts carries a copower decomposition of a restricted regular
module to one of the image. -/
private noncomputable def mapCopowerIso {I : Type*} [HasCoproductsOfShape I (Mod C R)]
    [HasCoproductsOfShape I (Mod D (F.obj R))]
    [PreservesColimitsOfShape (Discrete I) (F.mapMod R)]
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap a).obj (regular S)) :
    (∐ fun _ : I ↦ regular (F.obj R)) ≅ (comap (F.map a)).obj (regular (F.obj S)) :=
  Sigma.mapIso (fun _ ↦ (F.mapModRegularIso R).symm) ≪≫
    asIso (sigmaComparison (F.mapMod R) (fun _ : I ↦ regular R)) ≪≫
    (F.mapMod R).mapIso e ≪≫ mapRestrictedRegularIso F a

end MapCopower

section RingIso

variable {C : Type*} [Category C] [MonoidalCategory C]
  {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S']

private noncomputable def regularRingIso (r : R ≅ S) [IsMonHom r.hom] :
    (comap r.inv).obj (regular R) ≅ regular S :=
  (comapCongr (IsIso.Iso.inv_hom r).symm).app _ ≪≫ regularIsoOfIsIso r.hom

private noncomputable def restrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a) :
    (comap a').obj (regular S') ≅
      (comap r.inv).obj ((comap a).obj (regular S)) :=
  (comap a').mapIso (regularRingIso s).symm ≪≫
    ((comapComp a' s.inv).symm ≪≫ comapCongr h ≪≫ comapComp r.inv a).app _

private noncomputable def comapCopowerIso {I : Type*} [HasCoproductsOfShape I (Mod C R)]
    [HasCoproductsOfShape I (Mod C R')] (r : R ≅ R') [IsMonHom r.hom]
    [PreservesColimitsOfShape (Discrete I) (comap (D := C) r.inv)] :
    (comap r.inv).obj (∐ fun _ : I ↦ regular R) ≅ (∐ fun _ : I ↦ regular R') :=
  (asIso (sigmaComparison (comap r.inv) (fun _ : I ↦ regular R))).symm ≪≫
    Sigma.mapIso (fun _ ↦ regularRingIso r)

end RingIso

/-- If the restriction of the regular `S`-module along `φ : R ⟶ S` is a copower of the regular
`R`-module, then it is flat, so extension of scalars along `φ` is exact. -/
private theorem exact_of_copower {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] {I : Type v}
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap φ).obj (regular S)) :
    PreservesFiniteLimits (extendScalars φ) := by
  have h : ObjectProperty.flat ((comap φ).obj (regular S)) :=
    ObjectProperty.prop_of_iso _ e
      (ObjectProperty.flat_coproduct (fun _ : I ↦ 𝟙_ (Mod C R))
        (fun _ ↦ ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ (Mod C R)))))
  have : PreservesFiniteLimits (tensorLeft ((comap φ).obj (regular S))) := h.1.1
  have : PreservesFiniteLimits (extendScalars φ ⋙ forget S) :=
    preservesFiniteLimits_of_natIso (extendForgetTensorIso φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars φ) (forget S)

end CategoryTheory.Mod

namespace Profinite

open MonoidalCategory IntermediateField

private theorem preservesCoproducts_tensorLeft_presheaf (P : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) (tensorLeft P) := by
  apply preservesColimitsOfShape_of_evaluation
  intro U
  let ev := (evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj U
  have e : tensorLeft P ⋙ ev ≅ ev ⋙ tensorLeft (P.obj U) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact preservesColimitsOfShape_of_natIso e.symm

/-- A copower decomposition of the restricted regular module of presheaves of rings on profinite
sets sheafifies to one of the underlying condensed ring objects. -/
private noncomputable def sheafifyCopowerIso
    {S T : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}} (f : S ⟶ T)
    (I : Type (u + 1))
    [HasCoproductsOfShape I
      (Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (S.obj ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))]
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S))]
    (e : (∐ fun _ : I ↦ Mod.regular (S.obj ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ≅
      (Mod.comap (Functor.whiskerRight f.hom (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
        (Mod.regular (T.obj ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))) :
    (∐ fun _ : I ↦ Mod.regular ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)) ≅
      (Mod.comap ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f)).obj
        (Mod.regular ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj T)) := by
  let R := S.obj ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  let a := Functor.whiskerRight f.hom (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let sh := presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  have := preservesCoproducts_tensorLeft_presheaf R I
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete I)
      (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} _ _
  have : PreservesColimitsOfShape (Discrete I) (sh.mapMod R) := by
    have : PreservesColimitsOfShape (Discrete I) (sh.mapMod R ⋙ Mod.forget (sh.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I) (Mod.forget R ⋙ sh))
    have : ReflectsColimitsOfShape (Discrete I)
        (Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (sh.obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (sh.obj R))
  let r := Sheaf.sheafifyRingPresheafIso _ S
  let s := Sheaf.sheafifyRingPresheafIso _ T
  have ha : (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f ≫ s.inv =
      r.inv ≫ sh.map a := by
    rw [Sheaf.sheafCompose_map_eq]
    simp only [r, s, sh, a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : PreservesColimitsOfShape (Discrete I)
      (Mod.comap (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) r.inv) := by
    have : PreservesColimitsOfShape (Discrete I)
        (Mod.comap (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) r.inv ⋙
          Mod.forget ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I) (Mod.forget (sh.obj R)))
    have : ReflectsColimitsOfShape (Discrete I)
        (Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget _)
  exact ((Mod.restrictedRegularIsoOfRingIso (sh.map a) _ r s ha) ≪≫
    (Mod.comap r.inv).mapIso (Mod.mapCopowerIso sh a e).symm ≪≫ Mod.comapCopowerIso r).symm

/-! #### A finite basis: the extension `F/E` -/

private noncomputable def continuousAddHomPresheaf
    {S T : Type} [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Ring T] [TopologicalSpace T] [IsTopologicalRing T]
    (l : S →+ T) (hl : Continuous l) :
    continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} ⟶
      continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} where
  app U := AddCommGrpCat.ofHom
    { toFun f := ULift.up ⟨fun x ↦ l (f.down x), hl.comp f.down.continuous⟩
      map_zero' := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_zero l
      map_add' f g := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_add l _ _ }
  naturality _ _ _ := rfl

private noncomputable def continuousLinearPresheafHom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : S →ₗ[R] R) (hl : Continuous l) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ⟶
    Mod.regular (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up (⟨fun x ↦ l ((algebraMap R S (r.down x)) * s.down x), _⟩ :
      C(U.unop, R)) = ULift.up _
    congr 1
    ext x
    change l ((algebraMap R S (r.down x)) * s.down x) = r.down x * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousLinearPresheafHomFrom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : R →ₗ[R] S) (hl : Continuous l) :
    Mod.regular (continuousMapRingPresheaf.{u} R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ⟶
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up _ = ULift.up _
    congr 1
    ext x
    change l (r.down x * s.down x) = algebraMap R S (r.down x) * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

/-- A finite basis with continuous coordinates of a field extension `S/R` decomposes the
restricted regular module of presheaves `C(-, S)` into a finite direct sum of copies of the
regular module `C(-, R)`. -/
private noncomputable def continuousBasisIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ≅
    Mod.finiteFree (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) n := by
  let p (i : Fin n) := continuousLinearPresheafHom ha (b.coord i) (hc i)
  let q (i : Fin n) := continuousLinearPresheafHomFrom ha
    (LinearMap.toSpanSingleton R S (b i))
    (by
      change Continuous (fun r : R ↦ r • b i)
      simp_rw [Algebra.smul_def]
      exact ha.mul_const (b i))
  refine
    { hom := biproduct.lift p
      inv := biproduct.desc q
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [biproduct.lift_desc]
    apply Mod.hom_ext
    change (Mod.forget _).map (∑ i, p i ≫ q i) = _
    rw [Functor.map_sum]
    apply NatTrans.ext
    funext U
    simp only [NatTrans.app_sum]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    let ev : (AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S)) ⟶
        AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S))) →+ S :=
      { toFun g := (g.hom f).down x
        map_zero' := rfl
        map_add' _ _ := rfl }
    change ev (∑ i, _) = f.down x
    rw [map_sum]
    change (∑ i, (b.coord i (f.down x)) • b i) = f.down x
    exact b.sum_repr (f.down x)
  · apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      Category.id_comp]
    apply Mod.hom_ext
    by_cases hij : j = i
    · subst j
      rw [biproduct.ι_π_self]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b i) = f.down x
      simp
    · rw [biproduct.ι_π_ne _ hij]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = (0 : ULift.{u + 1} C(U.unop, R))
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b j) = 0
      simp [hij]

/-- For finite subextensions `E ≤ F`, the restricted regular module `F̲` over `E̲` is a finite
copower of the regular module: choose an `E`-basis of `F`, whose coordinates are continuous by
finite-dimensional linear topology over `ℚ_ℓ`, and sheafify the sectionwise decomposition. -/
private theorem exists_padicSubfield_point_basis (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (continuousMapRingObj E))] :
    ∃ I : Type (u + 1), Nonempty
      ((∐ fun _ : I ↦ Mod.regular (continuousMapRingObj.{u} E)) ≅
        (Mod.comap (padicSubfieldRingObjMap ℓ h)).obj
          (Mod.regular (continuousMapRingObj F))) := by
  classical
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E F
  let b := Module.finBasis E F
  have hb (i : Fin (Module.finrank E F)) : Continuous (b.coord i) :=
    ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  have ha : Continuous (algebraMap E F) := continuous_subtype_val.subtype_mk _
  let I := ULift.{u + 1} (Fin (Module.finrank E F))
  let R := continuousMapRingPresheaf.{u} E ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  have := preservesCoproducts_tensorLeft_presheaf R I
  let e : (∐ fun _ : I ↦ Mod.regular R) ≅
      (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap (algebraMap E F) ha)
        (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
        (Mod.regular (continuousMapRingPresheaf.{u} F ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
    Sigma.reindex Equiv.ulift (fun _ ↦ Mod.regular R) ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ (continuousBasisIso ha _ b hb).symm
  exact ⟨I, ⟨sheafifyCopowerIso (padicSubfieldCondensedRingMap ℓ h) I e⟩⟩

/-! #### A small basis: the extension `ℚ̄_ℓ/E` -/

section PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

private lemma coord_continuous_on_field {I : Type*} (b : Module.Basis I E (PadicAlgCl ℓ))
    (i : I) (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    Continuous (fun x : F ↦ b.coord i (x : PadicAlgCl ℓ)) := by
  let l := ((b.coord i).restrictScalars ℚ_[ℓ]).comp F.1.val.toLinearMap
  exact l.continuous_of_finiteDimensional

private lemma field_uniform_support {I : Type*} (b : Module.Basis I E (PadicAlgCl ℓ))
    (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ t : Finset I, ∀ x : F, (b.repr (x : PadicAlgCl ℓ)).support ⊆ t := by
  classical
  let c := Module.finBasis ℚ_[ℓ] F
  let t := Finset.univ.biUnion (fun j ↦ (b.repr (c j : PadicAlgCl ℓ)).support)
  refine ⟨t, fun x i hi ↦ ?_⟩
  by_contra hit
  have hz (j : Fin (Module.finrank ℚ_[ℓ] F)) : b.coord i (c j : PadicAlgCl ℓ) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hij
    exact hit (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩)
  have hzero : b.coord i (x : PadicAlgCl ℓ) = 0 := by
    rw [← c.sum_repr x]
    change (((b.coord i).restrictScalars ℚ_[ℓ]).comp F.1.val.toLinearMap)
      (∑ j, c.repr x j • c j) = 0
    simp only [map_sum, map_smul, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply]
    apply Finset.sum_eq_zero
    intro j _
    change _ • b.coord i (c j : PadicAlgCl ℓ) = 0
    rw [hz, smul_zero]
  exact (Finsupp.mem_support_iff.mp hi) hzero

private lemma section_coord_continuous {I : Type*} (b : Module.Basis I E (PadicAlgCl ℓ))
    (U : Profinite.{u}) (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) (i : I) :
    Continuous (fun x : U ↦ b.coord i ((f : C(U, PadicAlgCl ℓ)) x)) := by
  obtain ⟨F, hF, hf⟩ := f.property
  exact (coord_continuous_on_field ℓ E b i ⟨F, hF⟩).comp
    ((f : C(U, PadicAlgCl ℓ)).continuous.subtype_mk hf)

private noncomputable def sectionCoordinates {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u})
    (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) : I →₀ C(U, E) :=
  Finsupp.ofSupportFinite
    (fun i ↦ ⟨fun x ↦ b.coord i ((f : C(U, PadicAlgCl ℓ)) x),
      section_coord_continuous ℓ E b U f i⟩) (by
        classical
        obtain ⟨F, hF, hf⟩ := f.property
        obtain ⟨t, ht⟩ := field_uniform_support ℓ E b ⟨F, hF⟩
        apply t.finite_toSet.subset
        intro i hi
        by_contra hit
        apply hi
        apply ContinuousMap.ext
        intro x
        exact Finsupp.notMem_support_iff.mp
          (fun hm ↦ hit (ht ⟨(f : C(U, PadicAlgCl ℓ)) x, hf x⟩ hm)))

@[simp] private lemma sectionCoordinates_apply {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u})
    (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) (i : I) (t : U) :
    sectionCoordinates ℓ E b U f i t = b.coord i ((f : C(U, PadicAlgCl ℓ)) t) := by
  simp only [sectionCoordinates, Finsupp.ofSupportFinite_coe, ContinuousMap.coe_mk]

private noncomputable def scalarSection (U : Profinite.{u}) (x : PadicAlgCl ℓ)
    (f : C(U, E)) : PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
  ⟨⟨fun t ↦ (f t : PadicAlgCl ℓ) * x,
    (continuous_subtype_val.comp f.continuous).mul_const x⟩, by
      have hx : FiniteDimensional ℚ_[ℓ] ℚ_[ℓ]⟮x⟯ :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
      refine ⟨E.1 ⊔ ℚ_[ℓ]⟮x⟯, inferInstance, fun t ↦ ?_⟩
      exact mul_mem (IsConcreteLE.le_iff.mp le_sup_left (f t).property)
        (IsConcreteLE.le_iff.mp le_sup_right (IntermediateField.mem_adjoin_simple_self _ _))⟩

private noncomputable def scalarSectionHom (U : Profinite.{u}) (x : PadicAlgCl ℓ) :
    C(U, E) →+ PadicAlgCl.finiteIntermediateFieldValued ℓ U where
  toFun := scalarSection ℓ E U x
  map_zero' := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change (0 : PadicAlgCl ℓ) * x = 0
    exact zero_mul x
  map_add' f g := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change ((f t : PadicAlgCl ℓ) + g t) * x = (f t : PadicAlgCl ℓ) * x + g t * x
    exact add_mul _ _ _

private noncomputable def sectionCoordinatesHom {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ U →+ (I →₀ C(U, E)) where
  toFun := sectionCoordinates ℓ E b U
  map_zero' := by
    apply Finsupp.ext
    intro i
    apply ContinuousMap.ext
    intro t
    simp only [sectionCoordinates_apply, Finsupp.zero_apply, ContinuousMap.zero_apply]
    exact map_zero (b.coord i)
  map_add' f g := by
    apply Finsupp.ext
    intro i
    apply ContinuousMap.ext
    intro t
    simp only [sectionCoordinates_apply, Finsupp.add_apply, ContinuousMap.add_apply]
    exact map_add (b.coord i) _ _

private lemma sectionCoordinates_injective {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    Function.Injective (sectionCoordinatesHom ℓ E b U) := by
  intro f g h
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have he := congrArg (fun a : I →₀ C(U, E) ↦ a i t) h
  simpa only [sectionCoordinatesHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sectionCoordinates_apply, Module.Basis.coord_apply] using he

private lemma sectionCoordinates_scalarSection {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) (i : I) (f : C(U, E)) :
    sectionCoordinatesHom ℓ E b U (scalarSection ℓ E U (b i) f) = Finsupp.single i f := by
  classical
  apply Finsupp.ext
  intro j
  apply ContinuousMap.ext
  intro t
  simp only [sectionCoordinatesHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sectionCoordinates_apply]
  change b.coord j ((f t : PadicAlgCl ℓ) * b i) = (Finsupp.single i f) j t
  change b.coord j ((algebraMap E (PadicAlgCl ℓ)) (f t) * b i) = _
  rw [← Algebra.smul_def, map_smul]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Module.Basis.coord_apply, Ne.symm hij]

private noncomputable def sectionSum {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    (I →₀ C(U, E)) →+ PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
  Finsupp.liftAddHom (fun i ↦ scalarSectionHom ℓ E U (b i))

private lemma sectionCoordinates_sectionSum {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    (sectionCoordinatesHom ℓ E b U).comp (sectionSum ℓ E b U) = AddMonoidHom.id _ := by
  apply Finsupp.addHom_ext
  intro i f
  change sectionCoordinatesHom ℓ E b U (sectionSum ℓ E b U (Finsupp.single i f)) = _
  simpa only [sectionSum, Finsupp.liftAddHom_apply_single, scalarSectionHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.id_apply] using
      sectionCoordinates_scalarSection ℓ E b U i f

private noncomputable def sectionBasisEquiv {I : Type*}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    (I →₀ C(U, E)) ≃+ PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
  AddEquiv.ofBijective (sectionSum ℓ E b U) (by
    have h := sectionCoordinates_sectionSum ℓ E b U
    have hf : Function.LeftInverse (sectionCoordinatesHom ℓ E b U) (sectionSum ℓ E b U) :=
      DFunLike.congr_fun h
    refine ⟨hf.injective, fun f ↦ ⟨sectionCoordinatesHom ℓ E b U f, ?_⟩⟩
    apply sectionCoordinates_injective ℓ E b U
    exact hf _)

private noncomputable abbrev pointRPresheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  continuousMapRingPresheaf E ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}

private noncomputable abbrev pointSPresheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  padicAlgClRingPresheaf ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}

private noncomputable def scalarPresheaf (x : PadicAlgCl ℓ) :
    pointRPresheaf.{u} ℓ E ⟶ pointSPresheaf ℓ where
  app U := AddCommGrpCat.ofHom
    (ULift.ringEquiv.symm.toAddMonoidHom.comp
      ((scalarSectionHom ℓ E U.unop x).comp ULift.ringEquiv.toAddMonoidHom))
  naturality _ _ _ := rfl

private noncomputable abbrev pointMapPresheaf :
    pointRPresheaf.{u} ℓ E ⟶ pointSPresheaf ℓ :=
  Functor.whiskerRight (padicSubfieldToPadicAlgClRingPresheaf ℓ E)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})

private noncomputable def scalarModulePresheaf (x : PadicAlgCl ℓ) :
    Mod.regular (pointRPresheaf.{u} ℓ E) ⟶
      (Mod.comap (pointMapPresheaf ℓ E)).obj (Mod.regular (pointSPresheaf ℓ)) :=
  Mod.homMk (scalarPresheaf ℓ E x) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up _ = ULift.up _
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change ((r.down t : PadicAlgCl ℓ) * s.down t) * x =
      (r.down t : PadicAlgCl ℓ) * ((s.down t : PadicAlgCl ℓ) * x)
    exact mul_assoc _ _ _)

private noncomputable def basisPresheafCofan {I : Type (u + 1)}
    (b : Module.Basis I E (PadicAlgCl ℓ)) :
    Cofan (fun _ : I ↦ Mod.regular (pointRPresheaf.{u} ℓ E)) :=
  Cofan.mk ((Mod.comap (pointMapPresheaf ℓ E)).obj (Mod.regular (pointSPresheaf ℓ)))
    (fun i ↦ scalarModulePresheaf ℓ E (b i))

private noncomputable def basisPresheafCofanIsColimit {I : Type (u + 1)}
    (b : Module.Basis I E (PadicAlgCl ℓ)) : IsColimit (basisPresheafCofan ℓ E b) := by
  have := preservesCoproducts_tensorLeft_presheaf (pointRPresheaf ℓ E) I
  have : ReflectsColimitsOfShape (Discrete I)
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (pointRPresheaf ℓ E)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (pointRPresheaf ℓ E))
  apply evaluationJointlyReflectsColimits
  intro U
  let A := ULift.{u + 1} C(U.unop, E)
  let d := ModuleCat.finsuppCocone ℤ A I
  let hd := isColimitOfPreserves (forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1})
    (ModuleCat.finsuppCoconeIsColimit ℤ A I)
  let e : (I →₀ A) ≃+ ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ U.unop) :=
    (Finsupp.mapRange.addEquiv ULift.ringEquiv.toAddEquiv).trans
      ((sectionBasisEquiv ℓ E b U.unop).trans ULift.ringEquiv.symm.toAddEquiv)
  apply IsColimit.ofIsoColimit hd
  refine Cocone.ext (e.toAddCommGrpIso) ?_
  intro i
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  change e (Finsupp.single i.as f) = ULift.up (scalarSection ℓ E U.unop (b i.as) f.down)
  simp only [e, AddEquiv.trans_apply, Finsupp.mapRange.addEquiv_apply,
    Finsupp.mapRange_single]
  change ULift.up (sectionSum ℓ E b U.unop (Finsupp.single i.as f.down)) = _
  simp only [sectionSum, Finsupp.liftAddHom_apply_single]
  rfl

/-- The restricted regular module `ℚ̲̄_ℓ` over `E̲` is a copower of the regular module: choose an
algebraic `E`-basis of `ℚ̄_ℓ`. A section with values in a finite subextension has uniformly
finite support in this basis, its coordinates are continuous by finite-dimensional linear
topology, and finite sums of continuous coordinates times basis vectors are such sections.
This decomposes the presheaves sectionwise; sheafify. -/
theorem exists_padicAlgCl_point_basis
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (continuousMapRingObj E))] :
    ∃ I : Type (u + 1), Nonempty
      ((∐ fun _ : I ↦ Mod.regular (continuousMapRingObj.{u} E)) ≅
        (Mod.comap (padicSubfieldRingObjToPadicAlgCl ℓ E)).obj
          (Mod.regular (padicAlgClRingObj ℓ))) := by
  classical
  let I := ULift.{u + 1} (Module.Free.ChooseBasisIndex E (PadicAlgCl ℓ))
  let b : Module.Basis I E (PadicAlgCl ℓ) :=
    (Module.Free.chooseBasis E (PadicAlgCl ℓ)).reindex Equiv.ulift.symm
  have := preservesCoproducts_tensorLeft_presheaf (pointRPresheaf.{u} ℓ E) I
  let e : (∐ fun _ : I ↦ Mod.regular (pointRPresheaf.{u} ℓ E)) ≅
      (Mod.comap (pointMapPresheaf ℓ E)).obj (Mod.regular (pointSPresheaf ℓ)) :=
    (colimit.isColimit _).coconePointUniqueUpToIso (basisPresheafCofanIsColimit ℓ E b)
  have : HasCoproductsOfShape I (Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (pointRPresheaf.{u} ℓ E)) :=
    inferInstance
  exact ⟨I, ⟨@sheafifyCopowerIso _ _ (padicSubfieldCondensedRingToPadicAlgCl ℓ E) I
    (by exact this) _ e⟩⟩

end PadicAlgCl

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-! ### The coefficient rings `E_X`, `ℚ̄_ℓ,X` and their inclusions -/

section RingObj

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient ring object `E_X = p_X^* E̲` on `X_proét`, for a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev padicSubfieldRingObj (E : FiniteIntermediateField ℓ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj E) X

/-- The coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ` on `X_proét`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.padicAlgClRingObj ℓ) X

/-- The inclusion `E_X ⟶ F_X` for finite subextensions `E ≤ F`, the coefficient change induced by
the inclusion `E̲ ⟶ F̲` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObj X ℓ E ⟶ padicSubfieldRingObj X ℓ F :=
  coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X

/-- The inclusion `E_X ⟶ ℚ̄_ℓ,X` for a finite subextension `E`, the coefficient change induced by
the inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObj X ℓ E ⟶ padicAlgClRingObj X ℓ :=
  coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X

/-- The inclusion `E_X ⟶ F_X` followed by the inclusion `F_X ⟶ ℚ̄_ℓ,X` is the inclusion
`E_X ⟶ ℚ̄_ℓ,X`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjToPadicAlgCl X ℓ F =
      padicSubfieldRingObjToPadicAlgCl X ℓ E := by
  rw [← coefficientMap_comp, Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl]

/-- The inverse image `p_X^*` from condensed abelian groups is a left adjoint, being the
composite `π_X^* ∘ p^*` of two left adjoints. -/
instance isLeftAdjoint_upperStarFromPoint : (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

/-- The cocone over the diagram `E ↦ E_X` with vertex `ℚ̄_ℓ,X`, given by the inclusions
`E_X ⟶ ℚ̄_ℓ,X`: the image under `p_X^*` of `Profinite.padicAlgClRingObjCocone`. -/
noncomputable abbrev padicAlgClRingObjCocone :
    Cocone (Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X) :=
  (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)

/-- **`ℚ̄_ℓ,X = colim_E E_X`**: the inclusions `E_X ⟶ ℚ̄_ℓ,X` exhibit `ℚ̄_ℓ,X` as the filtered
colimit of the `E_X` in abelian pro-étale sheaves on `X`. This is the image of
`ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`) under the left adjoint
`p_X^*`. -/
noncomputable def isColimitPadicAlgClRingObjCocone : IsColimit (padicAlgClRingObjCocone X ℓ) :=
  isColimitOfPreserves (upperStarFromPoint X) (Profinite.isColimitPadicAlgClRingObjCocone ℓ)

end RingObj

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- If the restricted regular `S̲`-module along `a : R̲ ⟶ S̲` is a copower of the regular
`R̲`-module, then so is its pullback to any scheme `Z`, since `p_Z^*` is a monoidal left
adjoint; hence extension of scalars along `a_Z` is exact. -/
private theorem preservesFiniteLimits_extendScalars_of_pointCopower
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {I : Type (u + 1)}
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)]
    (e : (∐ fun _ : I ↦ Mod.regular R) ≅ (Mod.comap a).obj (Mod.regular S)) (Z : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z)) := by
  let F := upperStarFromPoint Z
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (F.obj R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasCoproducts.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (F.obj R)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete I) (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} _ _
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete I) (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} _ _
  have : PreservesColimitsOfShape (Discrete I) (MonoidalCategory.tensorLeft R) :=
    (ihom.adjunction R).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) (MonoidalCategory.tensorLeft (F.obj R)) :=
    (ihom.adjunction (F.obj R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) (F.mapMod R) := by
    have : PreservesColimitsOfShape (Discrete I) (Mod.forget R ⋙ F) :=
      comp_preservesColimitsOfShape _ _
    have : PreservesColimitsOfShape (Discrete I) (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I) (Mod.forget R ⋙ F))
    have : ReflectsColimitsOfShape (Discrete I)
        (Mod.forget (F.obj R) : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ ⥤ _) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (F.obj R))
  exact Mod.exact_of_copower (coefficientMap a Z) (Mod.mapCopowerIso F a e)

/-! ### Flatness of the coefficient inclusions -/

section Flat

variable (X : Scheme.{u})

/-- **(A0.2)** For finite subextensions `E ≤ F`, the extension of scalars along `E_X ⟶ F_X` is
exact: `F_X` is finite free, in particular flat, over `E_X`. See the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) := by
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) := IsGrothendieckAbelian.hasColimits _
  have : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  obtain ⟨I, ⟨e⟩⟩ := Profinite.exists_padicSubfield_point_basis.{u} ℓ h
  exact preservesFiniteLimits_extendScalars_of_pointCopower _ e X

/-- **(A0.2)** For a finite subextension `E`, the extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` is
exact: `ℚ̄_ℓ,X` is flat over `E_X`, being a filtered colimit of finite free `E_X`-modules. See
the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
    (E : FiniteIntermediateField ℓ) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) := by
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) := IsGrothendieckAbelian.hasColimits _
  have : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  obtain ⟨I, ⟨e⟩⟩ := Profinite.exists_padicAlgCl_point_basis.{u} ℓ E
  exact preservesFiniteLimits_extendScalars_of_pointCopower _ e X

end Flat

/-! ### (Push) and (Shriek) -/

section Push

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **(Push)** is an isomorphism for a finite extension `F/E`, on all unbounded objects: `F_X`
is finite free over `E_X`, so both sides are finite direct sums of copies of `Rf_*^E`. See the
module docstring. -/
instance isIso_derivedPushHom_padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsIso (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) f) :=
  have (Z : Scheme.{u}) : PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) Z)) :=
    preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap ℓ Z h
  -- term-mode `Exists.elim`: `obtain` on this existential times out at `isDefEq`
  (Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul.{u} ℓ h).elim
    fun _ hn ↦ hn.elim fun b hb ↦ isIso_derivedPushHom_of_isIso_biproductDesc_globalSmul
      (Profinite.padicSubfieldRingObjMap ℓ h) (Profinite.continuousMapConstRingHom F) b hb f

/-- **(Shriek)** is an isomorphism for a finite extension `F/E`, on all unbounded objects. -/
example [HasCompactification f] {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjMap ℓ h) f) :=
  inferInstance

end Push

end CondensedRing

end AlgebraicGeometry.ProEtale
