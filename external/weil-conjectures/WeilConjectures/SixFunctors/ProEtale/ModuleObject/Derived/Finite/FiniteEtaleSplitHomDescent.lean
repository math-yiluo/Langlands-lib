/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Tactic.CongrExclamation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Descent of module morphisms on finite etale splitting charts

Source: Stacks Project, Tags 03EM, 04TQ and 04HN; blueprint, stratified lattice trace proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction
  ProEtale.upperStar ProEtale.upperStarComp

/-- Agreement after every pair of weakly etale refinements over the same base map.
The comparisons use the specified inverse-image composition isomorphisms.
Source: Stacks Project, Tags 03EM and 04TQ.
(blueprint: lem-sfb-finite-etale-split-hom-descent) -/
@[irreducible]
def FiniteEtaleModuleChart.Compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {p : U ⟶ X}
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P) : Prop :=
  ∀ (c₁ c₂ : FiniteEtaleModuleChart p) (Z : Scheme.{u})
    (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) [WeaklyEtale a] [WeaklyEtale b]
    (w : a ≫ c₁.map = b ≫ c₂.map),
    (upperStarComp Λ a c₁.map).hom.app Q ≫ (upperStar Λ a).map (d c₁) ≫
        (upperStarComp Λ a c₁.map).inv.app P =
      ((eqToIso (congrArg (upperStar Λ) w)) ≪≫ upperStarComp Λ b c₂.map).hom.app Q ≫
        (upperStar Λ b).map (d c₂) ≫
      ((eqToIso (congrArg (upperStar Λ) w)) ≪≫ upperStarComp Λ b c₂.map).inv.app P

/-- Convert the usual local splitting into the sheet convention used here. -/
private theorem exists_split_chart
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] (x : X) :
    ∃ (c : FiniteEtaleModuleChart p) (y : c.base), Etale c.map ∧ c.map y = x := by
  classical
  obtain ⟨Y, g, y, hg, hy, J, V, ι, hJ, ⟨hc⟩, _, he⟩ :=
    finite_etale_etale_local_split p x
  let := hg
  let := hJ
  let := Fintype.ofFinite J
  choose e he using he
  let n := Fintype.card J
  let q : Fin n ≃ J := (Fintype.equivFin J).symm
  let b (k : Fin n) : Y ⟶ pullback p g := (e (q k)).inv ≫ ι (q k)
  have hb (k : Fin n) : b k ≫ pullback.snd p g = 𝟙 Y := by
    dsimp [b]
    rw [Category.assoc, ← he, Iso.inv_hom_id]
  let t (k : Fin n) := b k ≫ pullback.fst p g
  have w (k : Fin n) : t k ≫ p = g := by
    dsimp [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb, Category.id_comp]
  have hlift (k : Fin n) :
      pullback.lift (t k) (𝟙 Y) (by simpa using w k) = b k := by
    apply pullback.hom_ext <;> simp [t, hb]
  have hbcol : IsColimit (Cofan.mk (pullback p g) b) := by
    let K (c : Cofan (fun _ : Fin n ↦ Y)) : Cofan V :=
      Cofan.mk c.pt (fun j ↦ (e j).hom ≫ c.inj (q.symm j))
    refine Cofan.IsColimit.mk _ (fun c ↦ hc.desc (K c)) ?_ ?_
    · intro c k
      dsimp [b]
      have hf := hc.fac (K c) ⟨q k⟩
      change ι (q k) ≫ hc.desc (K c) = (e (q k)).hom ≫ c.inj _ at hf
      rw [Category.assoc, hf]
      simp
    · intro c m hm
      apply hc.hom_ext
      rintro ⟨j⟩
      change ι j ≫ m = ι j ≫ hc.desc (K c)
      have hf := hc.fac (K c) ⟨j⟩
      change ι j ≫ hc.desc (K c) = (e j).hom ≫ c.inj (q.symm j) at hf
      rw [hf]
      have h := hm (q.symm j)
      change ((e (q (q.symm j))).inv ≫ ι (q (q.symm j))) ≫ m = _ at h
      rw [q.apply_symm_apply] at h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun z ↦ (e j).hom ≫ z) h
  let c : FiniteEtaleModuleChart p :=
    { base := Y
      map := g
      weaklyEtale := inferInstance
      degree := n
      sheet := t
      over := w
      splits := by
        simpa only [hlift] using
          (show Nonempty (IsColimit (Cofan.mk _ b)) from ⟨hbcol⟩) }
  exact ⟨c, y, hg, hy⟩

/-- Chart pullbacks jointly reflect isomorphisms, including over the empty base. -/
private theorem split_chart_reflects_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    {Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : Q ⟶ P) (hf : ∀ c : FiniteEtaleModuleChart p,
      IsIso ((upperStar Λ c.map).map f)) : IsIso f := by
  classical
  choose c y hc hy using exists_split_chart p
  let (x : X) : Etale (c x).map := hc x
  have hcover : Presieve.ofArrows (fun x ↦ (c x).base) (fun x ↦ (c x).map) ∈
      Scheme.proetalePrecoverage X := by
    apply Scheme.etalePrecoverage_le_proetalePrecoverage
    exact (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨x, y x, hy x⟩, fun x ↦ hc x⟩
  have : IsIso f.hom := by
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom
      (fun x ↦ (c x).map) hcover
    intro x
    have := hf (c x)
    have h1 : IsIso ((ProEtale.upperStar Ab.{u + 1} (c x).map).map f.hom) := by
      apply (NatIso.isIso_map_iff
        (profinitePointModuleForgetPullbackIso Λ (c x).map) f).mp
      exact inferInstanceAs (IsIso ((Mod.forget _).map
        ((upperStar Λ (c x).map).map f)))
    exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction
      Ab.{u + 1} (c x).map inferInstance) f.hom).mp h1
  have : IsIso ((Mod.forget (condensedRingObj Λ X)).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Mod.forget (condensedRingObj Λ X))

/-- Underlying inverse image, normalized to literal restriction on the site. -/
private def moduleLocalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g] :
    upperStar Λ g ⋙ Mod.forget (condensedRingObj Λ Y) ≅
      Mod.forget (condensedRingObj Λ X) ⋙
        ProEtale.localizationRestriction Ab.{u + 1} g inferInstance :=
  profinitePointModuleForgetPullbackIso Λ g ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ X))
      (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance)

/-- Applying a functor and conjugating preserves an equation of morphisms. -/
private theorem normalize_map_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : C ⥤ E) (H : D ⥤ E) (S : F ⋙ H ≅ G)
    (Q P : C) {a b : F.obj Q ⟶ F.obj P} (h : a = b) :
    S.inv.app Q ≫ H.map a ≫ S.hom.app P =
      S.inv.app Q ≫ H.map b ≫ S.hom.app P := by
  cases h
  rfl

/-- Normalizing a composite module pullback is the composite normalization. -/
private theorem moduleLocalization_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (a : Z ⟶ Y) (g : Y ⟶ X) [WeaklyEtale a] [WeaklyEtale g]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((upperStarComp Λ a g).hom.app M).hom ≫
        (moduleLocalization Λ a).hom.app ((upperStar Λ g).obj M) ≫
        (ProEtale.localizationRestriction Ab.{u + 1} a inferInstance).map
          ((moduleLocalization Λ g).hom.app M) =
      (moduleLocalization Λ (a ≫ g)).hom.app M ≫
        (ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
          (a ≫ g) rfl inferInstance).hom.app M.X := by
  let F := ProEtale.upperStar Ab.{u + 1} a
  let L := ProEtale.localizationRestriction Ab.{u + 1} a inferInstance
  let α := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} a inferInstance
  have hm := (profinite_point_pullback_module_comparison Λ).2.2 Z Y X a g M
  have hs := NatTrans.congr_app
    (ProEtale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction_aux
      Ab.{u + 1} a g inferInstance inferInstance inferInstance) M.X
  dsimp only [moduleLocalization, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.whiskerRight_app, Mod.forget] at hs ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [← α.hom.naturality_assoc, ← α.hom.naturality]
  change ((upperStarComp Λ a g).hom.app M).hom ≫
    (profinitePointModuleForgetPullbackIso Λ a).hom.app ((upperStar Λ g).obj M) ≫
      (ProEtale.upperStar Ab.{u + 1} a).map
        ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) = _ at hm
  rw [reassoc_of% hm]
  exact congrArg (fun z ↦ (profinitePointModuleForgetPullbackIso Λ (a ≫ g)).hom.app M ≫ z) hs

/-- A commutative comparison square transports conjugated morphisms. -/
private theorem conjugate_comparison
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {a b c d : C} {x y q p q' p' : D}
    (eQ : q ≅ x) (eP : p ≅ y) (tQ : x ≅ L.obj a) (tP : y ≅ L.obj b)
    (sQ : a ≅ c) (sP : b ≅ d) (nQ : q ≅ q') (nP : p ≅ p')
    (cQ : q' ≅ L.obj c) (cP : p' ≅ L.obj d) (φ : a ⟶ b) (ψ : x ⟶ y)
    (hQ : eQ.hom ≫ tQ.hom ≫ L.map sQ.hom = nQ.hom ≫ cQ.hom)
    (hP : eP.hom ≫ tP.hom ≫ L.map sP.hom = nP.hom ≫ cP.hom)
    (hψ : ψ ≫ tP.hom = tQ.hom ≫ L.map φ) :
    nQ.inv ≫ eQ.hom ≫ ψ ≫ eP.inv ≫ nP.hom =
      cQ.hom ≫ L.map (sQ.inv ≫ φ ≫ sP.hom) ≫ cP.inv := by
  apply (cancel_epi nQ.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_mono cP.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [← reassoc_of% hQ, ← hP]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, L.map_comp]
  rw [reassoc_of% hψ]
  simp only [← L.map_comp_assoc, Iso.hom_inv_id_assoc, Category.comp_id]

/-- Transporting a local module map along a refinement commutes with normalization. -/
private theorem moduleLocalization_conj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (a : Z ⟶ Y) (g : Y ⟶ X) [WeaklyEtale a] [WeaklyEtale g]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : (upperStar Λ g).obj Q ⟶ (upperStar Λ g).obj P) :
    (moduleLocalization Λ (a ≫ g)).inv.app Q ≫
        (((upperStarComp Λ a g).hom.app Q ≫ (upperStar Λ a).map d ≫
          (upperStarComp Λ a g).inv.app P).hom) ≫
        (moduleLocalization Λ (a ≫ g)).hom.app P =
      (ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
        (a ≫ g) rfl inferInstance).hom.app Q.X ≫
      (ProEtale.localizationRestriction Ab.{u + 1} a inferInstance).map
        ((moduleLocalization Λ g).inv.app Q ≫ d.hom ≫
          (moduleLocalization Λ g).hom.app P) ≫
      (ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
        (a ≫ g) rfl inferInstance).inv.app P.X := by
  let L := ProEtale.localizationRestriction Ab.{u + 1} a inferInstance
  let C := ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
    (a ≫ g) rfl inferInstance
  let T := moduleLocalization Λ a
  have hnat := T.hom.naturality d
  change ((upperStar Λ a).map d).hom ≫ T.hom.app ((upperStar Λ g).obj P) =
    T.hom.app ((upperStar Λ g).obj Q) ≫ L.map d.hom at hnat
  have h := conjugate_comparison L
    ((Mod.forget _).mapIso ((upperStarComp Λ a g).app Q))
    ((Mod.forget _).mapIso ((upperStarComp Λ a g).app P))
    (T.app ((upperStar Λ g).obj Q)) (T.app ((upperStar Λ g).obj P))
    ((moduleLocalization Λ g).app Q) ((moduleLocalization Λ g).app P)
    ((moduleLocalization Λ (a ≫ g)).app Q) ((moduleLocalization Λ (a ≫ g)).app P)
    (C.app Q.X) (C.app P.X) d.hom (((upperStar Λ a).map d).hom)
    (moduleLocalization_comp Λ a g Q) (moduleLocalization_comp Λ a g P) hnat
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Mod.forget] at h
  simpa only [Mod.comp_hom', Category.assoc] using h

/-- The same normalization with an explicitly named common composite. -/
private theorem moduleLocalization_conj'
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (a : Z ⟶ Y) (g : Y ⟶ X) (k : Z ⟶ X) (hk : k = a ≫ g)
    [WeaklyEtale a] [WeaklyEtale g] [WeaklyEtale k]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : (upperStar Λ g).obj Q ⟶ (upperStar Λ g).obj P) :
    (moduleLocalization Λ k).inv.app Q ≫
        ((((eqToIso (congrArg (upperStar Λ) hk)) ≪≫ upperStarComp Λ a g).hom.app Q ≫
          (upperStar Λ a).map d ≫
          ((eqToIso (congrArg (upperStar Λ) hk)) ≪≫ upperStarComp Λ a g).inv.app P).hom) ≫
        (moduleLocalization Λ k).hom.app P =
      (ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
        k hk inferInstance).hom.app Q.X ≫
      (ProEtale.localizationRestriction Ab.{u + 1} a inferInstance).map
        ((moduleLocalization Λ g).inv.app Q ≫ d.hom ≫
          (moduleLocalization Λ g).hom.app P) ≫
      (ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
        k hk inferInstance).inv.app P.X := by
  cases hk
  simp only [eqToIso_refl, Iso.refl_trans, Functor.comp_obj, Mod.forget]
  exact moduleLocalization_conj Λ a g Q P d

/-- Evaluate composite restriction at the identity test object. -/
private theorem localization_component
    {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    (F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ψ : (ProEtale.localizationRestriction Ab.{u + 1} g inferInstance).obj F ⟶
      (ProEtale.localizationRestriction Ab.{u + 1} g inferInstance).obj G)
    (T : X.ProEt) (a : T.left ⟶ Y) (ha : a ≫ g = T.hom) [WeaklyEtale a] :
    let U₀ : T.left.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 T.left) inferInstance
    let ε : T ≅ (MorphismProperty.Over.map ⊤ T.prop).obj U₀ :=
      MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
    let C := ProEtale.localizationRestrictionComp Ab.{u + 1} a g inferInstance inferInstance
      T.hom ha.symm T.prop
    F.obj.map ε.inv.op ≫
        (C.hom.app F ≫
          (ProEtale.localizationRestriction Ab.{u + 1} a inferInstance).map ψ ≫
          C.inv.app G).hom.app (op U₀) ≫ G.obj.map ε.hom.op =
      F.obj.map (ProEtale.overMapIso g inferInstance T a ha).hom.op ≫
        ψ.hom.app (op _) ≫ G.obj.map (ProEtale.overMapIso g inferInstance T a ha).inv.op := by
  dsimp only
  simp only [Functor.id_obj, Functor.const_obj_obj, ProEtale.localizationRestriction,
    Functor.comp_obj, ProEtale.localizationRestrictionComp,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Iso.symm_inv, Iso.symm_hom, Iso.refl_trans,
    Iso.symm_mk, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.op_obj, NatTrans.op_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Category.assoc]
  let U₀ : T.left.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 T.left) inferInstance
  let ι₀ : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale a)).obj U₀ ⟶
      MorphismProperty.Over.mk ⊤ a
        (MorphismProperty.of_postcomp _ _ _ (inferInstance : WeaklyEtale g)
          (ha ▸ T.prop)) :=
    MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp a).symm trivial
  let κ₀ : MorphismProperty.Over.mk ⊤ a
      (MorphismProperty.of_postcomp _ _ _ (inferInstance : WeaklyEtale g)
        (ha ▸ T.prop)) ⟶
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale a)).obj U₀ :=
    MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp a) trivial
  have hκι : κ₀ ≫ ι₀ = 𝟙 _ := MorphismProperty.Over.Hom.ext (by simp [ι₀, κ₀])
  have hψa : ψ.hom.app (op (MorphismProperty.Over.mk ⊤ a
        (MorphismProperty.of_postcomp _ _ _ (inferInstance : WeaklyEtale g)
          (ha ▸ T.prop)))) =
      ((ProEtale.localizationRestriction Ab.{u + 1} g inferInstance).obj F).obj.map ι₀.op ≫
        ψ.hom.app (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale a)).obj U₀)) ≫
        ((ProEtale.localizationRestriction Ab.{u + 1} g inferInstance).obj G).obj.map κ₀.op := by
    rw [reassoc_of% ψ.hom.naturality ι₀.op, ← Functor.map_comp, ← op_comp, hκι,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [hψa]
  simp only [ProEtale.localizationRestriction, Functor.sheafPushforwardContinuous_obj_obj_map,
    ← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 2

private theorem proof_heq {A B : Prop} (a : A) (b : B) : HEq a b := by
  have h : A = B := propext ⟨fun _ ↦ b, fun _ ↦ a⟩
  cases h
  rfl

/-- Transport a compatibility equation to a common source functor. -/
private theorem compatible_commonMap_aux
    {C D : Type*} [Category C] [Category D] {F F₁ F₂ G₁ G₂ : C ⥤ D}
    (ha : F = F₁) (hb : F = F₂) (w : F₁ = F₂) (hw : ha.symm.trans hb = w)
    (c₁ : F₁ ≅ G₁) (c₂ : F₂ ≅ G₂) (Q P : C)
    (d₁ : G₁.obj Q ⟶ G₁.obj P) (d₂ : G₂.obj Q ⟶ G₂.obj P)
    (h : c₁.hom.app Q ≫ d₁ ≫ c₁.inv.app P =
      (eqToIso w ≪≫ c₂).hom.app Q ≫ d₂ ≫
        (eqToIso w ≪≫ c₂).inv.app P) :
    (eqToIso ha ≪≫ c₁).hom.app Q ≫ d₁ ≫ (eqToIso ha ≪≫ c₁).inv.app P =
      (eqToIso hb ≪≫ c₂).hom.app Q ≫ d₂ ≫ (eqToIso hb ≪≫ c₂).inv.app P := by
  cases hw
  cases ha
  simpa only [eqToIso_refl, Iso.refl_trans] using h

/-- Unpack one of the equations in chart compatibility. -/
private theorem compatible_pair
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {p : U ⟶ X}
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hd : FiniteEtaleModuleChart.Compatible Λ Q P d)
    (c₁ c₂ : FiniteEtaleModuleChart p) (Z : Scheme.{u})
    (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) [WeaklyEtale a] [WeaklyEtale b]
    (w : a ≫ c₁.map = b ≫ c₂.map) :
    (upperStarComp Λ a c₁.map).hom.app Q ≫ (upperStar Λ a).map (d c₁) ≫
        (upperStarComp Λ a c₁.map).inv.app P =
      (eqToIso (congrArg (upperStar Λ) w) ≪≫ upperStarComp Λ b c₂.map).hom.app Q ≫
        (upperStar Λ b).map (d c₂) ≫
        (eqToIso (congrArg (upperStar Λ) w) ≪≫ upperStarComp Λ b c₂.map).inv.app P := by
  delta FiniteEtaleModuleChart.Compatible at hd
  have h := hd c₁ c₂ Z a b w
  refine Eq.mp ?_ h
  run_tac Lean.Elab.Tactic.withMainContext do
    let step (g : Lean.MVarId) : Lean.MetaM (List Lean.MVarId) := g.withContext do
      if ← g.isAssigned then return []
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).cleanupAnnotations == t.cleanupAnnotations then
          g.assign (.fvar d.fvarId)
          return []
      if t.isForall then
        let (_, g) ← g.intro1P
        return [g]
      let g ← g.eqOfHEq
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let some (_, lhs, _, rhs) := t.heq? | throwError "expected heterogeneous equality: {t}"
      let lhs := lhs.cleanupAnnotations
      let rhs := rhs.cleanupAnnotations
      if lhs == rhs then
        g.hrefl
        return []
      if (← Lean.Meta.isProof lhs) && (← Lean.Meta.isProof rhs) then
        g.assign (← Lean.Meta.mkAppM ``proof_heq #[lhs, rhs])
        return []
      if lhs.isLambda && rhs.isLambda then
        let g ← g.heqOfEq
        return ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``funext)
      let f := lhs.getAppFn
      let f' := rhs.getAppFn
      let xs := lhs.getAppArgs
      let ys := rhs.getAppArgs
      unless f == f' && xs.size == ys.size && !xs.isEmpty do
        throwError "cannot compare {lhs} and {rhs} by syntactic congruence"
      let info ← Lean.Meta.getFunInfoNArgs f xs.size
      let fixed := xs.zipWith (fun x y ↦ x.cleanupAnnotations == y.cleanupAnnotations) ys
      let c ← Lean.Meta.mkRichHCongr (forceHEq := true) (← Lean.Meta.inferType f) info
        (fixedFun := true) (fixedParams := fixed)
      g.apply (c.proof.beta #[f])
    let mut todo := #[← Lean.Elab.Tactic.getMainGoal]
    for _ in [:10000] do
      if todo.isEmpty then break
      let g := todo.back!
      todo := todo.pop
      todo := todo ++ (← step g).toArray
    unless todo.isEmpty do throwError "syntactic congruence did not finish"
    Lean.Elab.Tactic.replaceMainGoal []

/-- Chart compatibility also holds when both composites are identified with a third map. -/
private theorem compatible_commonMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {p : U ⟶ X}
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hd : FiniteEtaleModuleChart.Compatible Λ Q P d)
    (c₁ c₂ : FiniteEtaleModuleChart p) (Z : Scheme.{u})
    (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) [WeaklyEtale a] [WeaklyEtale b]
    (k : Z ⟶ X) (ha : k = a ≫ c₁.map) (hb : k = b ≫ c₂.map) :
    ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a c₁.map).hom.app Q ≫
        (upperStar Λ a).map (d c₁) ≫
        ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a c₁.map).inv.app P =
      ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b c₂.map).hom.app Q ≫
        (upperStar Λ b).map (d c₂) ≫
        ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b c₂.map).inv.app P := by
  have h := compatible_commonMap_aux (congrArg (upperStar Λ) ha) (congrArg (upperStar Λ) hb)
    (congrArg (upperStar Λ) (ha.symm.trans hb)) rfl
    (upperStarComp Λ a c₁.map) (upperStarComp Λ b c₂.map) Q P
    ((upperStar Λ a).map (d c₁)) ((upperStar Λ b).map (d c₂))
    (compatible_pair Λ Q P d hd c₁ c₂ Z a b (ha.symm.trans hb))
  dsimp only [Functor.comp_obj] at h ⊢
  refine Eq.mp ?_ h
  run_tac Lean.Elab.Tactic.withMainContext do
    let step (g : Lean.MVarId) : Lean.MetaM (List Lean.MVarId) := g.withContext do
      if ← g.isAssigned then return []
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).cleanupAnnotations == t.cleanupAnnotations then
          g.assign (.fvar d.fvarId)
          return []
      if t.isForall then
        let (_, g) ← g.intro1P
        return [g]
      let g ← g.eqOfHEq
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let some (_, lhs, _, rhs) := t.heq? | throwError "expected heterogeneous equality: {t}"
      let lhs := lhs.cleanupAnnotations
      let rhs := rhs.cleanupAnnotations
      if lhs == rhs then
        g.hrefl
        return []
      if (← Lean.Meta.isProof lhs) && (← Lean.Meta.isProof rhs) then
        g.assign (← Lean.Meta.mkAppM ``proof_heq #[lhs, rhs])
        return []
      if lhs.isLambda && rhs.isLambda then
        let g ← g.heqOfEq
        return ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``funext)
      let f := lhs.getAppFn
      let f' := rhs.getAppFn
      let xs := lhs.getAppArgs
      let ys := rhs.getAppArgs
      unless f == f' && xs.size == ys.size && !xs.isEmpty do
        throwError "cannot compare {lhs} and {rhs} by syntactic congruence"
      let info ← Lean.Meta.getFunInfoNArgs f xs.size
      let fixed := xs.zipWith (fun x y ↦ x.cleanupAnnotations == y.cleanupAnnotations) ys
      let c ← Lean.Meta.mkRichHCongr (forceHEq := true) (← Lean.Meta.inferType f) info
        (fixedFun := true) (fixedParams := fixed)
      g.apply (c.proof.beta #[f])
    let mut todo := #[← Lean.Elab.Tactic.getMainGoal]
    for _ in [:10000] do
      if todo.isEmpty then break
      let g := todo.back!
      todo := todo.pop
      todo := todo ++ (← step g).toArray
    unless todo.isEmpty do throwError "syntactic congruence did not finish"
    Lean.Elab.Tactic.replaceMainGoal []

/-- Glue literal restrictions on all charts by the sheaf of morphisms. -/
private theorem split_chart_glue_sheaf
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p]
    (F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ψ : ∀ c : FiniteEtaleModuleChart p,
      (ProEtale.localizationRestriction Ab.{u + 1} c.map inferInstance).obj F ⟶
        (ProEtale.localizationRestriction Ab.{u + 1} c.map inferInstance).obj G)
    (hψ : ∀ (c k : FiniteEtaleModuleChart p) (T : X.ProEt)
      (a : T.left ⟶ c.base) (b : T.left ⟶ k.base)
      (ha : a ≫ c.map = T.hom) (hb : b ≫ k.map = T.hom),
      F.obj.map (ProEtale.overMapIso c.map inferInstance T a ha).hom.op ≫
          (ψ c).hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso c.map inferInstance T a ha).inv.op =
        F.obj.map (ProEtale.overMapIso k.map inferInstance T b hb).hom.op ≫
          (ψ k).hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso k.map inferInstance T b hb).inv.op) :
    ∃ φ : F ⟶ G, ∀ c,
      (ProEtale.localizationRestriction Ab.{u + 1} c.map inferInstance).map φ = ψ c := by
  classical
  let H := presheafHom F.obj G.obj
  let V' : FiniteEtaleModuleChart p → X.ProEt := fun c ↦
    MorphismProperty.Over.mk ⊤ c.map inferInstance
  let top : X.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let π : ∀ c, V' c ⟶ top := fun c ↦
    MorphismProperty.Over.homMk c.map (Category.comp_id _) trivial
  have hw : ∀ c (T : Over (V' c)), T.hom.left ≫ c.map = T.left.hom :=
    fun c T ↦ MorphismProperty.Over.w T.hom
  let Φ : ∀ c, Over (V' c) ⥤ c.base.ProEt := fun c ↦
    { obj T := MorphismProperty.Over.mk ⊤ T.hom.left
        (MorphismProperty.of_postcomp _ _ _ c.weaklyEtale (by
          rw [hw c T]; exact T.left.prop))
      map g := MorphismProperty.Over.homMk g.left.left
        (congrArg (fun f ↦ f.left) (Over.w g)) trivial }
  let κ : ∀ c, Φ c ⋙ MorphismProperty.Over.map ⊤ c.weaklyEtale ≅ Over.forget (V' c) :=
    fun c ↦ NatIso.ofComponents (fun T ↦
      ProEtale.overMapIso c.map inferInstance T.left T.hom.left (hw c T))
      (fun g ↦ by ext; simp [ProEtale.overMapIso, Φ])
  let x : ∀ c, H.obj (op (V' c)) := fun c ↦
    (Functor.isoWhiskerRight (NatIso.op (κ c)) F.obj).hom ≫
      Functor.whiskerLeft (Φ c).op (ψ c).hom ≫
        (Functor.isoWhiskerRight (NatIso.op (κ c)) G.obj).inv
  have hx : Presieve.Arrows.Compatible H π x := by
    intro c k Z a b _
    refine NatTrans.ext (funext fun T ↦ ?_)
    exact hψ c k T.unop.left _ _
      (hw c ((Over.map a).obj T.unop)) (hw k ((Over.map b).obj T.unop))
  have hH : Presheaf.IsSheaf (Scheme.ProEt.topology X) H :=
    Presheaf.IsSheaf.hom F.obj G.obj G.property
  have hcov : Sieve.generate (Presieve.ofArrows V' π) ∈
      Scheme.ProEt.topology X top := by
    choose c y hc hy using exists_split_chart p
    have hsmall : Presieve.ofArrows (fun x ↦ V' (c x)) (fun x ↦ π (c x)) ∈
        Scheme.ProEt.precoverage X top := by
      rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      apply Scheme.etalePrecoverage_le_proetalePrecoverage
      exact (Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ ⟨x, y x, hy x⟩, fun x ↦ hc x⟩
    apply Scheme.ProEt.mem_topology_iff.mpr
    refine ⟨_, hsmall, ?_⟩
    rintro Z f ⟨x⟩
    exact Sieve.le_generate _ _ _ ⟨c x⟩
  have hsf : (Presieve.ofArrows V' π).IsSheafFor H := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ _).mp hH _ hcov
  obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf x hx
  let toTop : ∀ V : X.ProEt, V ⟶ top := fun V ↦
    MorphismProperty.Over.homMk V.hom (Category.comp_id _) trivial
  have htop : ∀ {V : X.ProEt} (f : V ⟶ top), f = toTop V := fun f ↦
    MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let s : H.sections := ⟨fun V ↦ H.map (toTop V.unop).op t, fun {V V'} f ↦ by
    simp only [← Functor.map_comp_apply]
    rw [show (toTop V.unop).op ≫ f = (f.unop ≫ toTop V.unop).op from rfl,
      htop (f.unop ≫ toTop V.unop)]⟩
  refine ⟨⟨presheafHomSectionsEquiv _ _ s⟩, ?_⟩
  intro c
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  let g₀ : (MorphismProperty.Over.map ⊤ c.weaklyEtale).obj W.unop ⟶ V' c :=
    MorphismProperty.Over.homMk W.unop.hom rfl trivial
  have h := congrArg (fun α ↦ α.app (op (Over.mk g₀))) (ht c)
  have hκ : ProEtale.overMapIso c.map inferInstance _ g₀.left (hw c (Over.mk g₀)) =
      Iso.refl _ := by ext; rfl
  dsimp only [x] at h
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.op_hom, NatIso.op_inv,
    NatTrans.op_app] at h
  have h₁ : (κ c).hom.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.hom hκ
  have h₂ : (κ c).inv.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.inv hκ
  rw [h₁, h₂] at h
  erw [op_id, F.obj.map_id, G.obj.map_id, Category.id_comp, Category.comp_id] at h
  refine Eq.trans ?_ h
  change t.app (op (Over.mk (𝟙 _ ≫ toTop _))) = t.app (op (Over.mk (g₀ ≫ π c)))
  rw [htop (𝟙 _ ≫ toTop _), htop (g₀ ≫ π c)]

/-- The inverse images on splitting charts jointly detect equality of sheaf maps. -/
private theorem split_chart_sheaf_hom_ext
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p]
    {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (f g : F ⟶ G)
    (h : ∀ c : FiniteEtaleModuleChart p,
      (ProEtale.upperStar Ab.{u + 1} c.map).map f =
        (ProEtale.upperStar Ab.{u + 1} c.map).map g) : f = g := by
  classical
  choose c y hc hy using exists_split_chart p
  let (x : X) : Etale (c x).map := hc x
  have hcover : Presieve.ofArrows (fun x ↦ (c x).base) (fun x ↦ (c x).map) ∈
      Scheme.proetalePrecoverage X := by
    apply Scheme.etalePrecoverage_le_proetalePrecoverage
    exact (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨x, y x, hy x⟩, fun x ↦ hc x⟩
  have hj : JointlyFaithful (fun x ↦ ProEtale.upperStar Ab.{u + 1} (c x).map) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N φ hφ
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} φ
      (fun x ↦ (c x).map) hcover
    intro x
    exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction
      Ab.{u + 1} (c x).map inferInstance) φ).mp (hφ x)
  exact hj.map_injective (fun x ↦ h (c x))

open CategoryTheory.MonoidalCategory

open scoped CategoryTheory.MonObj in
/-- A linear map between mapped modules gives the pulled-back action equation. -/
private theorem map_action_identity
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {R : C} [MonObj R] (Q P : Mod C R)
    (φ : Q.X ⟶ P.X) (δ : (F.mapMod R).obj Q ⟶ (F.mapMod R).obj P)
    (hδ : F.map φ = δ.hom) :
    F.map (γ[R, Q.X] ≫ φ) = F.map (R ◁ φ ≫ γ[R, P.X]) := by
  rw [F.map_comp, F.map_comp]
  apply (cancel_epi (Functor.LaxMonoidal.μ F R Q.X)).mp
  erw [← Category.assoc, ← F.mapMod_obj_smul Q, hδ]
  erw [← Functor.LaxMonoidal.μ_natural_right_assoc, hδ]
  exact CategoryTheory.IsModHom.smul_hom (f := δ.hom)

/-- A sheaf map that is locally a module map is globally a module map. -/
private theorem split_chart_linear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (φ : Q.X ⟶ P.X)
    (hφ : ∀ c, (ProEtale.localizationRestriction Ab.{u + 1} c.map inferInstance).map φ =
      (moduleLocalization Λ c.map).inv.app Q ≫ (d c).hom ≫
        (moduleLocalization Λ c.map).hom.app P) :
    CategoryTheory.IsModHom (condensedRingObj Λ X) φ := by
  classical
  unfold upperStar at d
  constructor
  apply split_chart_sheaf_hom_ext p
  intro c
  let F := ProEtale.upperStar Ab.{u + 1} c.map
  let α := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} c.map inferInstance
  let R := condensedRingObj Λ X
  let A := condensedPullbackHom Λ c.map
  let E := Mod.extendScalars A
  let e := Mod.extendScalarsIsoComapInv A
  have : (Mod.comap (D := Sheaf (Scheme.ProEt.topology c.base) Ab.{u + 1})
      (asIso A).inv).IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso A).inverse.IsEquivalence
  have : E.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let δ : (F.mapMod R).obj Q ⟶ (F.mapMod R).obj P := E.preimage (d c)
  have hδ : F.map φ = δ.hom := by
    have he := congrArg Mod.Hom.hom (e.hom.naturality δ)
    change (E.map δ).hom ≫ (e.hom.app ((F.mapMod R).obj P)).hom =
      (e.hom.app ((F.mapMod R).obj Q)).hom ≫ δ.hom at he
    have hmap : E.map δ = d c := E.map_preimage (d c)
    rw [hmap] at he
    have hδ₀ : (e.inv.app ((F.mapMod R).obj Q)).hom ≫ (d c).hom ≫
        (e.hom.app ((F.mapMod R).obj P)).hom = δ.hom := by
      rw [he, ← Category.assoc]
      have hid := congrArg Mod.Hom.hom (e.inv_hom_id_app ((F.mapMod R).obj Q))
      rw [Mod.comp_hom'] at hid
      rw [hid]
      exact Category.id_comp _
    have hc := hφ c
    dsimp only [moduleLocalization, profinitePointModuleForgetPullbackIso, Iso.trans_inv,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Mod.forget] at hc
    erw [Category.assoc] at hc
    change (ProEtale.localizationRestriction Ab.{u + 1} c.map inferInstance).map φ =
      α.inv.app Q.X ≫ (e.inv.app ((F.mapMod R).obj Q)).hom ≫ (d c).hom ≫
        (e.hom.app ((F.mapMod R).obj P)).hom ≫ α.hom.app P.X at hc
    have hn := α.hom.naturality φ
    rw [hc, Iso.hom_inv_id_app_assoc, reassoc_of% hδ₀] at hn
    exact (cancel_mono (α.hom.app P.X)).mp hn
  exact map_action_identity F Q P φ δ hδ

/-- Normalize the module compatibility equation on a common test scheme. -/
private theorem split_chart_normalized_overlap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {p : U ⟶ X}
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hd : FiniteEtaleModuleChart.Compatible Λ Q P d)
    (c k : FiniteEtaleModuleChart p) (T : X.ProEt)
    (a : T.left ⟶ c.base) (b : T.left ⟶ k.base)
    (ha : a ≫ c.map = T.hom) (hb : b ≫ k.map = T.hom)
    [WeaklyEtale a] [WeaklyEtale b] :
    let ψ := fun c : FiniteEtaleModuleChart p ↦
      (moduleLocalization Λ c.map).inv.app Q ≫ (d c).hom ≫
        (moduleLocalization Λ c.map).hom.app P
    (ProEtale.localizationRestrictionComp Ab.{u + 1} a c.map inferInstance inferInstance
      T.hom ha.symm T.prop).hom.app Q.X ≫
      (ProEtale.localizationRestriction Ab.{u + 1} a inferInstance).map (ψ c) ≫
      (ProEtale.localizationRestrictionComp Ab.{u + 1} a c.map inferInstance inferInstance
        T.hom ha.symm T.prop).inv.app P.X =
    (ProEtale.localizationRestrictionComp Ab.{u + 1} b k.map inferInstance inferInstance
      T.hom hb.symm T.prop).hom.app Q.X ≫
      (ProEtale.localizationRestriction Ab.{u + 1} b inferInstance).map (ψ k) ≫
      (ProEtale.localizationRestrictionComp Ab.{u + 1} b k.map inferInstance inferInstance
        T.hom hb.symm T.prop).inv.app P.X := by
  have h := compatible_commonMap Λ Q P d hd c k T.left a b T.hom ha.symm hb.symm
  have h' := normalize_map_eq (upperStar (X := T.left) (Y := X) Λ T.hom)
    (Mod.forget (condensedRingObj Λ X) ⋙
      ProEtale.localizationRestriction (U := X) (V := T.left) Ab.{u + 1} T.hom T.prop)
    (Mod.forget (condensedRingObj Λ T.left))
    (moduleLocalization (X := X) (Y := T.left) Λ T.hom) Q P h
  dsimp only [Functor.comp_obj, Mod.forget] at h'
  exact (moduleLocalization_conj' Λ a c.map T.hom ha.symm Q P (d c)).symm.trans
    (h'.trans (moduleLocalization_conj' Λ b k.map T.hom hb.symm Q P (d k)))

/-- The normalized chart morphisms are a matching family of sheaf morphisms. -/
private theorem split_chart_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {p : U ⟶ X}
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hd : FiniteEtaleModuleChart.Compatible Λ Q P d) :
    let ψ := fun c : FiniteEtaleModuleChart p ↦
      (moduleLocalization Λ c.map).inv.app Q ≫ (d c).hom ≫
        (moduleLocalization Λ c.map).hom.app P
    ∀ (c k : FiniteEtaleModuleChart p) (T : X.ProEt)
      (a : T.left ⟶ c.base) (b : T.left ⟶ k.base)
      (ha : a ≫ c.map = T.hom) (hb : b ≫ k.map = T.hom),
      Q.X.obj.map (ProEtale.overMapIso c.map inferInstance T a ha).hom.op ≫
          (ψ c).hom.app (op _) ≫
          P.X.obj.map (ProEtale.overMapIso c.map inferInstance T a ha).inv.op =
        Q.X.obj.map (ProEtale.overMapIso k.map inferInstance T b hb).hom.op ≫
          (ψ k).hom.app (op _) ≫
          P.X.obj.map (ProEtale.overMapIso k.map inferInstance T b hb).inv.op := by
  dsimp only
  let ψ (c : FiniteEtaleModuleChart p) :=
    (moduleLocalization Λ c.map).inv.app Q ≫ (d c).hom ≫
      (moduleLocalization Λ c.map).hom.app P
  intro c k T a b ha hb
  have : WeaklyEtale (a ≫ c.map) := ha ▸ T.prop
  have : WeaklyEtale a := WeaklyEtale.of_comp a c.map
  have : WeaklyEtale (b ≫ k.map) := hb ▸ T.prop
  have : WeaklyEtale b := WeaklyEtale.of_comp b k.map
  have h' := split_chart_normalized_overlap Λ Q P d hd c k T a b ha hb
  let U₀ : T.left.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 T.left) inferInstance
  let ε : T ≅ (MorphismProperty.Over.map ⊤ T.prop).obj U₀ :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  have h'' := congrArg (fun f ↦ Q.X.obj.map ε.inv.op ≫
    f.hom.app (op U₀) ≫ P.X.obj.map ε.hom.op) h'
  rw [localization_component c.map Q.X P.X (ψ c) T a ha,
    localization_component k.map Q.X P.X (ψ k) T b hb] at h''
  exact h''

/-- Existence half of finite-etale compatible Hom descent.
Source: Stacks Project, Tags 03EM, 04TQ and 04HN.
(blueprint: lem-sfb-finite-etale-split-hom-descent-existence) -/
theorem finiteEtaleSplitHom_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hd : FiniteEtaleModuleChart.Compatible Λ Q P d) :
    ∃ f : Q ⟶ P, ∀ c, (upperStar Λ c.map).map f = d c := by
  classical
  let ψ (c : FiniteEtaleModuleChart p) :=
    (moduleLocalization Λ c.map).inv.app Q ≫ (d c).hom ≫
      (moduleLocalization Λ c.map).hom.app P
  obtain ⟨φ, hφ⟩ := split_chart_glue_sheaf p Q.X P.X ψ
    (split_chart_compatible Λ Q P d hd)
  have : CategoryTheory.IsModHom (condensedRingObj Λ X) φ :=
    split_chart_linear Λ p Q P d φ hφ
  let f : Q ⟶ P := ⟨φ⟩
  refine ⟨f, fun c ↦ ?_⟩
  apply (Mod.forget (condensedRingObj Λ c.base)).map_injective
  have hn := (moduleLocalization Λ c.map).hom.naturality f
  change ((upperStar Λ c.map).map f).hom ≫ (moduleLocalization Λ c.map).hom.app P =
    (moduleLocalization Λ c.map).hom.app Q ≫
      (ProEtale.localizationRestriction Ab.{u + 1} c.map inferInstance).map φ at hn
  rw [hφ c] at hn
  simp only [ψ, Iso.hom_inv_id_app_assoc] at hn
  exact (cancel_mono ((moduleLocalization Λ c.map).hom.app P)).mp hn

/-- Local surjectivity criterion for the epi half.
Source: Stacks Project, Tags 03EM, 04TQ and 04HN.
(blueprint: lem-sfb-finite-etale-split-hom-descent-local-surjective) -/
theorem finiteEtaleSplitHom_local_surjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : Q ⟶ P)
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hf : ∀ c, (upperStar Λ c.map).map f = d c)
    (hd : ∀ c, Epi (d c)) : Sheaf.IsLocallySurjective f.hom := by
  let := HasZeroObject.zero'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  have hepi (c : FiniteEtaleModuleChart p) : Epi ((upperStar Λ c.map).map f) := by
    rw [hf c]
    exact hd c
  have hzero : IsZero (cokernel f) := by
    have : IsIso (0 : cokernel f ⟶ 0) := by
      apply split_chart_reflects_iso Λ p
      intro c
      let L := upperStar Λ c.map
      have := hepi c
      have hz : IsZero (cokernel (L.map f)) := isZero_cokernel_of_epi _
      have hsrc : IsZero (L.obj (cokernel f)) := hz.of_iso (PreservesCokernel.iso L f)
      have htgt : IsZero (L.obj 0) := L.map_isZero (isZero_zero _)
      exact isIso_of_source_target_iso_zero _ hsrc.isoZero htgt.isoZero
    exact (isZero_zero _).of_iso (asIso (0 : cokernel f ⟶ 0))
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hzero
  have : Epi f.hom := inferInstanceAs (Epi ((Mod.forget _).map f))
  exact (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} f.hom).mpr inferInstance

/-- Epi half of finite-etale compatible Hom descent.
Source: Stacks Project, Tags 03EM, 04TQ and 04HN.
(blueprint: lem-sfb-finite-etale-split-hom-descent-epi) -/
theorem finiteEtaleSplitHom_epi
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : Q ⟶ P)
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hf : ∀ c, (upperStar Λ c.map).map f = d c)
    (hd : ∀ c, Epi (d c)) : Epi f := by
  have hloc := finiteEtaleSplitHom_local_surjective Λ p Q P f d hf hd
  have hepi : Epi f.hom :=
    (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} f.hom).mp hloc
  exact Functor.epi_of_epi_map (Mod.forget (condensedRingObj Λ X)) hepi

theorem finiteEtaleSplitHom_descent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (hd : FiniteEtaleModuleChart.Compatible Λ Q P d) :
    ∃ f : Q ⟶ P, (∀ c, (upperStar Λ c.map).map f = d c) ∧
      ((∀ c, Epi (d c)) → Epi f) := by
  obtain ⟨f, hf⟩ := finiteEtaleSplitHom_exists Λ p Q P d hd
  refine ⟨f, hf, ?_⟩
  exact fun h ↦ finiteEtaleSplitHom_epi Λ p Q P f d hf h

end AlgebraicGeometry.ProEtale.CondensedRing
