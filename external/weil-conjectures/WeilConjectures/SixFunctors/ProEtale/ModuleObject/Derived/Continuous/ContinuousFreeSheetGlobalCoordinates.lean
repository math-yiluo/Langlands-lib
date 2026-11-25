/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleLatticeSheetMaps
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Global scalar-compatible frames with independent ranks

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2.
(blueprint: lem-sfb-continuous-free-sheet-global-coordinates)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Include integral continuous vector coordinates in rational continuous coordinates.
Source: the coefficient inclusion in the blueprint local computation.
(blueprint: lem-sfb-continuous-free-sheet-global-coordinates) -/
def continuousIntegralVector {E : Type} [NormedField E] (A : Subring E)
    {Z : Type u} [TopologicalSpace Z] {r : ℕ} (x : C(Z, Fin r → A)) :
    C(Z, Fin r → E) :=
  ⟨fun z i ↦ (x z i : E), continuous_pi fun i ↦
    continuous_subtype_val.comp ((continuous_apply i).comp x.continuous)⟩

section
variable (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [TotallyDisconnectedSpace A]
attribute [local irreducible] continuousRingModuleEquivalence continuousRingRegularIso

private def vectorAddEquiv (B : X.ProEt) (n : ℕ) :
    (Fin n → ULift.{u + 1} C(B.left, A)) ≃+ C(B.left, Fin n → A) where
  toFun x := ContinuousMap.pi (fun i ↦ (x i).down)
  invFun x i := ULift.up ((ContinuousMap.eval i).comp x)
  left_inv x := by ext i z; rfl
  right_inv x := by ext z i; rfl
  map_add' x y := by ext z i; rfl

private def freeSectionIso (n : ℕ) (B : X.ProEt) :
    ((continuousRingModuleEquivalence X A).functor.obj
      (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj A) X) n)).val.obj
        (op B) ≅ ModuleCat.of ((continuousMapRingSheaf X A).obj.obj (op B))
          (Fin n → (continuousMapRingSheaf X A).obj.obj (op B)) := by
  let F := (continuousRingModuleEquivalence X A).functor
  let H := F ⋙ SheafOfModules.evaluation (continuousMapRingSheaf X A) (op B)
  let : H.Additive := Functor.additive_of_preserves_binary_products H
  let : PreservesBiproduct (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) H :=
    preservesBiproduct_of_preservesProduct H
  exact H.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦
    (SheafOfModules.evaluation (continuousMapRingSheaf X A) (op B)).mapIso
      (continuousRingRegularIso X A)) ≪≫ ModuleCat.biproductIsoPi _

private theorem freeSectionIso_apply (n : ℕ) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj
      (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj A) X) n)).val.obj
        (op B)) (i : Fin n) :
    (freeSectionIso X A n B).hom x i =
      (continuousRingRegularIso X A).hom.val.app (op B)
        (((continuousRingModuleEquivalence X A).functor.map
          (biproduct.π (fun _ : Fin n ↦ Mod.regular
            (condensedRingObj (Profinite.continuousMapRingObj A) X)) i)).val.app
          (op B) x) := by
  let F := (continuousRingModuleEquivalence X A).functor
  let H := F ⋙ SheafOfModules.evaluation (continuousMapRingSheaf X A) (op B)
  let : H.Additive := Functor.additive_of_preserves_binary_products H
  let : PreservesBiproduct (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) H :=
    preservesBiproduct_of_preservesProduct H
  have hp (f : Fin n → ModuleCat.{u + 1} ((continuousMapRingSheaf X A).obj.obj (op B))) :
      (ModuleCat.biproductIsoPi f).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
        biproduct.π f i := by
    apply (cancel_epi (ModuleCat.biproductIsoPi f).inv).1
    simp
  let f : Fin n → ModuleCat.{u + 1} ((continuousMapRingSheaf X A).obj.obj (op B)) :=
    fun _ ↦ (SheafOfModules.evaluation (continuousMapRingSheaf X A) (op B)).obj
      (SheafOfModules.unit (continuousMapRingSheaf X A))
  let q := H.mapBiproduct (fun _ : Fin n ↦ Mod.regular
    (condensedRingObj (Profinite.continuousMapRingObj A) X)) ≪≫
      biproduct.mapIso (fun _ ↦
        (SheafOfModules.evaluation (continuousMapRingSheaf X A) (op B)).mapIso
          (continuousRingRegularIso X A))
  change ((q.hom ≫ (ModuleCat.biproductIsoPi f).hom) x) i = _
  have hp' := hp f
  have he := congrArg (fun k ↦ (q.hom ≫ k) x) hp'
  change ((q.hom ≫ (ModuleCat.biproductIsoPi f).hom) x) i =
    (q.hom ≫ biproduct.π f i) x at he
  rw [he]
  dsimp only [q, f, Iso.trans_hom]
  rw [Category.assoc, biproduct.mapIso_hom, biproduct.map_π,
    ← Category.assoc, Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]
  rfl

private def freePresentation (n : ℕ) :
    ContinuousFunctionPresentation X A (Fin n → A)
      (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj A) X) n) where
  sections B := (CategoryTheory.Iso.toLinearEquiv (freeSectionIso X A n B)).toAddEquiv.trans
    (vectorAddEquiv X A B n)
  restrict B D a x := by
    ext z i
    change ((freeSectionIso X A n D).hom
      (((continuousRingModuleEquivalence X A).functor.obj _).val.map a.op x) i).down z =
      ((freeSectionIso X A n B).hom x i).down (a.left.base.hom z)
    rw [freeSectionIso_apply, freeSectionIso_apply]
    have h := PresheafOfModules.naturality_apply
      ((continuousRingModuleEquivalence X A).functor.map
        (biproduct.π (fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (Profinite.continuousMapRingObj A) X)) i)).val a.op x
    rw [h]
    have h' := PresheafOfModules.naturality_apply
      (continuousRingRegularIso X A).hom.val a.op
      (((continuousRingModuleEquivalence X A).functor.map
        (biproduct.π (fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (Profinite.continuousMapRingObj A) X)) i)).val.app (op B) x)
    exact congrArg (fun y ↦ y.down z) h'
  smul B a x := by
    ext z i
    have h := (freeSectionIso X A n B).hom.hom.map_smul
      (show (continuousMapRingSheaf X A).obj.obj (op B) from a) x
    exact congrArg (fun y ↦ (y i).down z) h

private def framePresentation
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))
    (n : ℕ) (e : Q ≅ Mod.finiteFree
      (condensedRingObj (Profinite.continuousMapRingObj A) X) n) :
    ContinuousFunctionPresentation X A (Fin n → A) Q where
  sections B := (CategoryTheory.Iso.toLinearEquiv
    ((SheafOfModules.evaluation _ (op B)).mapIso
      ((continuousRingModuleEquivalence X A).functor.mapIso e))).toAddEquiv.trans
        ((freePresentation X A n).sections B)
  restrict B D a x := by
    change (freePresentation X A n).sections D
      (((continuousRingModuleEquivalence X A).functor.map e.hom).val.app (op D)
        (((continuousRingModuleEquivalence X A).functor.obj Q).val.map a.op x)) = _
    rw [PresheafOfModules.naturality_apply, (freePresentation X A n).restrict]
    rfl
  smul B a x := by
    change (freePresentation X A n).sections B
      (((continuousRingModuleEquivalence X A).functor.map e.hom).val.app (op B) (a • x)) = _
    rw [map_smul, (freePresentation X A n).smul]
    rfl

end

section
variable (X : Scheme.{u})
  {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]
private def freeExtensionIso (n : ℕ) :
    (Mod.extendScalars (coefficientMap a X)).obj
      (Mod.finiteFree (condensedRingObj R X) n) ≅
        Mod.finiteFree (condensedRingObj S X) n :=
  Mod.finiteFreeIsoMap _ (Mod.regularExtensionIso (coefficientMap a X)) n
private theorem freeExtensionIso_projection (n : ℕ) (i : Fin n) :
    (freeExtensionIso X a n).hom ≫
        biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj S X)) i =
      (Mod.extendScalars (coefficientMap a X)).map
          (biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj R X)) i) ≫
        (Mod.regularExtensionIso (coefficientMap a X)).hom := by
  simp only [freeExtensionIso, Mod.finiteFreeIsoMap, Iso.trans_hom, Category.assoc,
    biproduct.mapIso_hom, biproduct.map_π, Functor.mapBiproduct_hom]
  rw [← Category.assoc]
  erw [biproduct.lift_π]
private theorem regularExtensionIso_unit :
    (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app
        (Mod.regular (condensedRingObj R X)) ≫
      (Mod.comap (coefficientMap a X)).map
        (Mod.regularExtensionIso (coefficientMap a X)).hom =
      Mod.regularCoefficientMap (coefficientMap a X) := by
  apply Mod.hom_ext
  exact Mod.extendUnitHom_extendHom _ _
private theorem freeExtensionIso_unit_projection (n : ℕ) (i : Fin n) :
    (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app
        (Mod.finiteFree (condensedRingObj R X) n) ≫
      (Mod.comap (coefficientMap a X)).map
        ((freeExtensionIso X a n).hom ≫
          biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj S X)) i) =
      biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj R X)) i ≫
        Mod.regularCoefficientMap (coefficientMap a X) := by
  rw [freeExtensionIso_projection, Functor.map_comp, ← Category.assoc]
  have hn := (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.naturality
    (biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj R X)) i)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← hn, Category.assoc, regularExtensionIso_unit]
end

section
private def explicitComapIso (X : Scheme.{u}) (T S : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [TotallyDisconnectedSpace S]
    (φ : T →+* S) (hφ : Continuous φ) :
    Mod.comap ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap φ hφ))) ⋙
      (continuousRingModuleEquivalence X T).functor ≅
    (continuousRingModuleEquivalence X S).functor ⋙
      SheafOfModules.restrictScalars (continuousMapRingSheafMap X φ hφ) := by
  let J := Scheme.ProEt.topology X
  let RT := continuousMapRingSheaf X T
  let RS := continuousMapRingSheaf X S
  let AT := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RT
  let AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RS
  letI : IsCommMonObj AT := Sheaf.isCommMonObj_sheafCompose_obj J RT
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  letI : IsCommMonObj AS := Sheaf.isCommMonObj_sheafCompose_obj J RS
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, S)) inferInstance a b)
  let α := (upperStarFromPoint X).map
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ))
  let β := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X φ hφ)
  have hc : inv (chartComparison X T) ≫ α = β ≫ inv (chartComparison X S) := by
    apply (cancel_epi (chartComparison X T)).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← chartComparison_naturality X T S φ hφ]
    simp
    rfl
  let e₀ : Mod.comap α ⋙ Mod.comap (inv (chartComparison X T)) ≅
      Mod.comap (inv (chartComparison X S)) ⋙ Mod.comap β :=
    (Mod.comapComp _ _).symm ≪≫ Mod.comapCongr hc ≪≫ Mod.comapComp _ _
  let FT := (InternalAbelianSheafModule.sectionModuleEquivalence J AT).functor
  let FS := (InternalAbelianSheafModule.sectionModuleEquivalence J AS).functor
  let GT := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RT).symm).functor
  let GS := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RS).symm).functor
  let e₁ := sectionModuleComapIso X β
  let e₂ : SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (sectionRingMap X β)) ⋙ GT ≅
      GS ⋙ SheafOfModules.restrictScalars (continuousMapRingSheafMap X φ hφ) := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
      · refine ModuleCat.isoMk (Iso.refl _) ?_
        intro r
        ext m
        rfl
      · intro Z W f
        ext
        rfl
    · intro M N f
      ext Z m
      rfl
  refine NatIso.ofComponents (fun M ↦
    (FT ⋙ GT).mapIso (e₀.app M) ≪≫
      GT.mapIso (e₁.app ((Mod.comap (inv (chartComparison X S))).obj M)) ≪≫
      e₂.app (FS.obj ((Mod.comap (inv (chartComparison X S))).obj M))) ?_
  intro M N f
  ext Z m
  rfl

variable (X : Scheme.{u}) (A E : Type)
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
  [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
  (φ : A →+* E) (hφ : Continuous φ)
-- The two encodings have the same underlying abelian sheaf.
private def restrictSections
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) (B : X.ProEt) :
    ((continuousRingModuleEquivalence X A).functor.obj ((Mod.comap ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap φ hφ)))).obj Q)).val.obj
      (op B) ≃+ ((continuousRingModuleEquivalence X E).functor.obj Q).val.obj (op B) :=
  { toFun := fun x ↦ x
    invFun := fun x ↦ x
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl }
-- Reduce the explicit comparison only for its sectionwise scalar equation.
private theorem restricted_smul
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj ((Mod.comap ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap φ hφ)))).obj Q)).val.obj
      (op B)) (a : ULift.{u + 1} C(B.left, A)) :
    restrictSections X A E φ hφ Q B (a • x) =
      ((continuousMapRingSheafMap X φ hφ).hom.app (op B) a) •
        restrictSections X A E φ hφ Q B x := by
  exact (((explicitComapIso X A E φ hφ).hom.app Q).val.app (op B)).hom.map_smul
    (show (continuousMapRingSheaf X A).obj.obj (op B) from a) x

private theorem restrictSections_naturality
    (Q V : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (f : Q ⟶ V) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj
      ((Mod.comap ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap φ hφ)))).obj Q)).val.obj (op B)) :
    restrictSections X A E φ hφ V B
      (((continuousRingModuleEquivalence X A).functor.map
        ((Mod.comap ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap φ hφ)))).map f)).val.app (op B) x) =
      ((continuousRingModuleEquivalence X E).functor.map f).val.app (op B)
        (restrictSections X A E φ hφ Q B x) := by
  rfl

end

private theorem adjointSheetNormalization
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')
    (F : C ⥤ C') (G : D ⥤ D') (δ : R ⋙ F ⟶ G ⋙ R')
    (ρ : F ⋙ L' ⟶ L ⋙ G) (M : C)
    (h : F.map (adj.unit.app M) ≫ δ.app (L.obj M) =
      adj'.unit.app (F.obj M) ≫ R'.map (ρ.app M))
    {Q : D} {V : D'} (e : L.obj M ⟶ Q) (k : G.obj Q ⟶ V) :
    F.map ((adj.homEquiv M Q) e) ≫ δ.app Q ≫ R'.map k =
      adj'.unit.app (F.obj M) ≫ R'.map (ρ.app M ≫ G.map e ≫ k) := by
  rw [Adjunction.homEquiv_unit, F.map_comp]
  simp only [Category.assoc]
  have hn := δ.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (F.map (R.map e)), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (adj.unit.app M)), h]
  simp only [Functor.map_comp, Category.assoc]

section
attribute [local irreducible] upperStar upperStarComp comapUpperStarIso pullIso
  Mod.extendScalars Mod.extendRestrictAdjunction
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
  (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
  (p : U ⟶ X)
  (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
  (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
  (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
private def sheetExtensionIso :
    (Mod.extendScalars (coefficientMap a Y)).obj ((upperStar R t).obj M) ≅
      (upperStar S g).obj P := by
  subst g
  exact (pullIso a t).app M ≪≫ (upperStar S t).mapIso e ≪≫
    ((upperStarComp S t p).app P).symm
-- The equality compares the full composed module pullback normalizations.
private theorem sheetEmbedding_unit :
    finiteEtaleLatticeSheetEmbedding a P p M e g t w =
      (Mod.extendRestrictAdjunction (coefficientMap a Y)).unit.app
          ((upperStar R t).obj M) ≫
        (Mod.comap (coefficientMap a Y)).map (sheetExtensionIso a P p M e g t w).hom := by
  subst g
  exact adjointSheetNormalization
      (Mod.extendRestrictAdjunction (coefficientMap a U))
      (Mod.extendRestrictAdjunction (coefficientMap a Y))
      (upperStar R t) (upperStar S t) (comapUpperStarIso a t).inv (pullIso a t).hom M
      (upperStar_map_unit_comp_comapUpperStarIso_inv_app a t M) e.hom
      ((upperStarComp S t p).inv.app P)

end

section
attribute [local irreducible] continuousRingModuleEquivalence continuousRingRegularIso
variable (X : Scheme.{u}) (E : Type) [CommRing E] [TopologicalSpace E]
  [IsTopologicalRing E] [TotallyDisconnectedSpace E]
  {Q V : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E) X)}
  {n r : ℕ} (p : ContinuousFunctionPresentation X E (Fin n → E) Q)
  (q : ContinuousFunctionPresentation X E (Fin r → E) V) (e : Q ≅ V)
private theorem presentation_symm_smul (B : X.ProEt) (a : C(B.left, E))
    (x : C(B.left, Fin n → E)) :
    (p.sections B).symm (a • x) = (ULift.up a) • (p.sections B).symm x := by
  apply (p.sections B).injective
  rw [AddEquiv.apply_symm_apply, p.smul, AddEquiv.apply_symm_apply]
private def presentationChange (B : X.ProEt) :
    C(B.left, Fin n → E) ≃ₗ[C(B.left, E)] C(B.left, Fin r → E) := by
  let m := (((SheafOfModules.evaluation _ (op B)).mapIso
    ((continuousRingModuleEquivalence X E).functor.mapIso e))).toLinearEquiv
  let f := (p.sections B).symm.trans (m.toAddEquiv.trans (q.sections B))
  refine { f with map_smul' := ?_ }
  intro a x
  change q.sections B (m ((p.sections B).symm (a • x))) = _
  rw [presentation_symm_smul, m.map_smul, q.smul]
  rfl
private theorem presentationChange_sections (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X E).functor.obj Q).val.obj (op B)) :
    presentationChange X E p q e B (p.sections B x) =
      q.sections B
        (((continuousRingModuleEquivalence X E).functor.map e.hom).val.app (op B) x) := by
  change q.sections B
    (((continuousRingModuleEquivalence X E).functor.map e.hom).val.app (op B)
      ((p.sections B).symm (p.sections B x))) = _
  rw [AddEquiv.symm_apply_apply]
private theorem presentationChange_naturality (B D : X.ProEt) (a : D ⟶ B)
    (x : C(B.left, Fin n → E)) :
    presentationChange X E p q e D (x.comp a.left.base.hom) =
      (presentationChange X E p q e B x).comp a.left.base.hom := by
  have h : (p.sections D).symm (x.comp a.left.base.hom) =
      ((continuousRingModuleEquivalence X E).functor.obj Q).val.map a.op
        ((p.sections B).symm x) := by
    apply (p.sections D).injective
    rw [AddEquiv.apply_symm_apply, p.restrict, AddEquiv.apply_symm_apply]
  change q.sections D
    (((continuousRingModuleEquivalence X E).functor.map e.hom).val.app (op D)
      ((p.sections D).symm (x.comp a.left.base.hom))) = _
  rw [h, PresheafOfModules.naturality_apply, q.restrict]
  rfl
end

private theorem encodeMap_apply (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (f : M ⟶ N) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj M).val.obj (op B)) :
    ((continuousRingModuleEquivalence X A).functor.map f).val.app (op B) x =
      f.hom.hom.app (op B) x := by rfl
private theorem regularCoordinate_apply (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj A) X))).val.obj (op B)) :
    (continuousRingRegularIso X A).hom.val.app (op B) x =
      (chartComparison X A).hom.app (op B) x := by rfl
private theorem freeCoordinate_apply (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (n : ℕ) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj
      (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj A) X) n)).val.obj
        (op B)) (i : Fin n) (z : B.left) :
    (freePresentation X A n).sections B x z i =
      ((chartComparison X A).hom.app (op B)
        ((biproduct.π (fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (Profinite.continuousMapRingObj A) X)) i).hom.hom.app
            (op B) x)).down z := by
  change ((freeSectionIso X A n B).hom x i).down z = _
  rw [freeSectionIso_apply, encodeMap_apply, regularCoordinate_apply]

private theorem freeExtension_coordinate
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) (n : ℕ) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X (continuousIntegers l E)).functor.obj
      (Mod.finiteFree (condensedRingObj (integralCoeff l E) X) n)).val.obj (op B)) :
    (freePresentation X E n).sections B
      (((Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap l E) X)).unit.app
          (Mod.finiteFree (condensedRingObj (integralCoeff l E) X) n) ≫
        (Mod.comap (coefficientMap (integralScalarMap l E) X)).map
          (freeExtensionIso X (integralScalarMap l E) n).hom).hom.hom.app (op B) x) =
      continuousIntegralVector (continuousIntegers l E)
        ((freePresentation X (continuousIntegers l E) n).sections B x) := by
  ext z i
  rw [freeCoordinate_apply]
  change ((chartComparison X E).hom.app (op B)
      ((biproduct.π (fun _ : Fin n ↦ Mod.regular
        (condensedRingObj (Profinite.continuousMapRingObj E) X)) i).hom.hom.app (op B)
          (((Mod.extendRestrictAdjunction
              (coefficientMap (integralScalarMap l E) X)).unit.app
              (Mod.finiteFree (condensedRingObj (integralCoeff l E) X) n) ≫
            (Mod.comap (coefficientMap (integralScalarMap l E) X)).map
              (freeExtensionIso X (integralScalarMap l E) n).hom).hom.hom.app
                (op B) x))).down z = _
  have h := congrArg (fun f ↦ f.hom.hom.app (op B) x)
    (freeExtensionIso_unit_projection X (integralScalarMap l E) n i)
  change (biproduct.π (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) i).hom.hom.app (op B)
        (((Mod.extendRestrictAdjunction
            (coefficientMap (integralScalarMap l E) X)).unit.app
            (Mod.finiteFree (condensedRingObj (integralCoeff l E) X) n) ≫
          (Mod.comap (coefficientMap (integralScalarMap l E) X)).map
            (freeExtensionIso X (integralScalarMap l E) n).hom).hom.hom.app (op B) x) =
      (coefficientMap (integralScalarMap l E) X).hom.app (op B)
        ((biproduct.π (fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (integralCoeff l E) X)) i).hom.hom.app (op B) x) at h
  rw [h]
  let y := (biproduct.π (fun _ : Fin n ↦ Mod.regular
    (condensedRingObj (integralCoeff l E) X)) i).hom.hom.app (op B) x
  have hc := congrArg (fun f ↦ f.hom.app (op B) y)
    (chartComparison_naturality X (continuousIntegers l E) E
      (continuousIntegers l E).subtype continuous_subtype_val)
  change (chartComparison X E).hom.app (op B)
      ((coefficientMap (integralScalarMap l E) X).hom.app (op B) y) =
    (continuousMapRingSheafMap X (continuousIntegers l E).subtype
      continuous_subtype_val).hom.app (op B) ((chartComparison X _).hom.app (op B) y) at hc
  rw [hc]
  change (((chartComparison X (continuousIntegers l E)).hom.app (op B) y).down z : E) =
    (((freePresentation X (continuousIntegers l E) n).sections B x z i :
      continuousIntegers l E) : E)
  rw [freeCoordinate_apply]

private theorem freeExtension_coordinate_encoded
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) (n : ℕ) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X (continuousIntegers l E)).functor.obj
      (Mod.finiteFree (condensedRingObj (integralCoeff l E) X) n)).val.obj (op B)) :
    (freePresentation X E n).sections B
      (restrictSections X (continuousIntegers l E) E (continuousIntegers l E).subtype
        continuous_subtype_val
        (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj E) X) n) B
        (((continuousRingModuleEquivalence X (continuousIntegers l E)).functor.map
          ((Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap l E) X)).unit.app
              (Mod.finiteFree (condensedRingObj (integralCoeff l E) X) n) ≫
            (Mod.comap (coefficientMap (integralScalarMap l E) X)).map
              (freeExtensionIso X (integralScalarMap l E) n).hom)).val.app (op B) x)) =
      continuousIntegralVector (continuousIntegers l E)
        ((freePresentation X (continuousIntegers l E) n).sections B x) := by
  exact freeExtension_coordinate l E X n B x

private def restrictPresentation (X : Scheme.{u}) (E : Type) [NormedField E]
    [TotallyDisconnectedSpace E] (A : Subring E)
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (r : ℕ) (p : ContinuousFunctionPresentation X E (Fin r → E) Q) :
    ContinuousFunctionPresentation X A (Fin r → E)
      ((Mod.comap (coefficientMap
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap A.subtype continuous_subtype_val)) X)).obj Q)
    where
  sections B := (restrictSections X A E A.subtype continuous_subtype_val Q B).trans
    (p.sections B)
  restrict B D a x := p.restrict B D a x
  smul B a x := by
    change p.sections B
      (restrictSections X A E A.subtype continuous_subtype_val Q B (a • x)) = _
    rw [restricted_smul, p.smul]
    rfl

private theorem restrictPresentation_sections (X : Scheme.{u}) (E : Type) [NormedField E]
    [TotallyDisconnectedSpace E] (A : Subring E)
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (r : ℕ) (p : ContinuousFunctionPresentation X E (Fin r → E) Q) (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj
      ((Mod.comap (coefficientMap
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap A.subtype continuous_subtype_val)) X)).obj
              Q)).val.obj (op B)) :
    (restrictPresentation X E A Q r p).sections B x =
      p.sections B (restrictSections X A E A.subtype continuous_subtype_val Q B x) := by
  rfl

attribute [local irreducible] continuousRingModuleEquivalence continuousRingRegularIso
  upperStar upperStarComp comapUpperStarIso pullIso Mod.extendScalars Mod.extendRestrictAdjunction

private theorem freeCoordinates
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [TotallyDisconnectedSpace E] (Y : Scheme.{u})
    (Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y))
    (d : ℕ) (N : Fin d → Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) Y))
    (q : ∀ j, (Mod.extendScalars (coefficientMap (integralScalarMap l E) Y)).obj (N j) ≅ Q)
    (hP : Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj E) Y) Q)
    (hM : ∀ j, Mod.IsFree (condensedRingObj (integralCoeff l E) Y) (N j)) :
    ∃ (r : ℕ) (n : Fin d → ℕ) (c : ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → E) ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj Q))
      (b : ∀ j, ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin (n j) → continuousIntegers l E) (N j))
      (F : ∀ (j : Fin d) (B : Y.ProEt),
        C(B.left, Fin (n j) → E) ≃ₗ[C(B.left, E)] C(B.left, Fin r → E)),
      (∀ (j : Fin d) (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin (n j) → E)),
        F j D (x.comp a.left.base.hom) = (F j B x).comp a.left.base.hom) ∧
      ∀ (j : Fin d) (B : Y.ProEt)
        (x : ((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.obj
          (N j)).val.obj (op B)),
        c.sections B
          (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
            ((Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap l E) Y)).unit.app
              (N j) ≫ (Mod.comap (coefficientMap (integralScalarMap l E) Y)).map
                (q j).hom)).val.app (op B) x) =
          F j B (continuousIntegralVector (continuousIntegers l E) ((b j).sections B x)) := by
  classical
  obtain ⟨r, ⟨er⟩⟩ := hP
  choose n hn using hM
  let en j := Classical.choice (hn j)
  let A := continuousIntegers l E
  let S := Profinite.continuousMapRingObj E
  let a := integralScalarMap l E
  let α := coefficientMap a Y
  let z (j : Fin d) : Mod.finiteFree (condensedRingObj S Y) (n j) ≅ Q :=
    (freeExtensionIso Y a (n j)).symm ≪≫
      (Mod.extendScalars α).mapIso (en j).symm ≪≫
        q j
  let cp := framePresentation Y E Q r er
  let c := restrictPresentation Y E A Q r cp
  let b j := framePresentation Y A (N j) (n j) (en j)
  let fp j := freePresentation Y E (n j)
  let F j B := presentationChange Y E (fp j) cp (z j) B
  refine ⟨r, n, c, b, F, ?_, ?_⟩
  · intro j B D a x
    exact presentationChange_naturality Y E (fp j) cp (z j) B D a x
  · intro j B x
    let η := (Mod.extendRestrictAdjunction α).unit
    let k := η.app (Mod.finiteFree (condensedRingObj (integralCoeff l E) Y) (n j)) ≫
      (Mod.comap α).map (freeExtensionIso Y a (n j)).hom
    have hs : η.app (N j) ≫ (Mod.comap α).map (q j).hom =
        (en j).hom ≫ k ≫ (Mod.comap α).map (z j).hom := by
      have he : (Mod.extendScalars α).map (en j).hom ≫
          (freeExtensionIso Y a (n j)).hom ≫ (z j).hom =
          (q j).hom := by
        dsimp only [z, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
          Functor.mapIso_inv]
        rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← Functor.map_comp,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
      have hn := η.naturality (en j).hom
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      rw [← he]
      simpa only [Functor.map_comp, Category.assoc, k] using
        congrArg (fun f ↦ f ≫
          (Mod.comap α).map (freeExtensionIso Y a (n j)).hom ≫
            (Mod.comap α).map (z j).hom) hn.symm
    let y := ((continuousRingModuleEquivalence Y A).functor.map (en j).hom).val.app
      (op B) x
    have hu := freeExtension_coordinate_encoded l E Y (n j) B y
    change (freePresentation Y E (n j)).sections B
      (restrictSections Y A E A.subtype continuous_subtype_val
        (Mod.finiteFree (condensedRingObj S Y) (n j)) B
        (((continuousRingModuleEquivalence Y A).functor.map k).val.app (op B) y)) =
      continuousIntegralVector A ((b j).sections B x) at hu
    change (restrictPresentation Y E A Q r cp).sections B _ = _
    erw [restrictPresentation_sections]
    rw [hs]
    simp only [Functor.map_comp, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [restrictSections_naturality]
    exact (presentationChange_sections Y E (fp j) cp (z j) B _).symm.trans
      (congrArg (F j B) hu)

attribute [local semireducible] continuousRingModuleEquivalence continuousRingRegularIso

-- Instantiate the abstract frames with the concrete module pullback constructions.
/-- Global free frames give natural rational coordinate changes before extracting matrices.
This assertion concerns the base Y itself, with no restriction to open subschemes.
Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2;
Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-continuous-free-sheet-global-coordinates)

Proof. Choose a finite free rational frame and integral frames for the finitely
many pulled-back modules. Extend each integral frame to E and compare it with the
rational frame as follows. The component of pullIso on M identifies the extension
of t_j*M with t_j*Ext(M); follow by t_j*e, then by the inverse of upperStarComp
normalized by w j, obtaining an isomorphism q_j from Ext(t_j*M) to g*P.
The continuous coefficient encoding takes these finite biproducts to finite products
of the continuous coefficient sheaf. Keep the rank r of the rational frame and
the independent ranks n j of the integral frames. No rank identification or
pointwise evaluation is needed.
The encoded rational coordinate changes are the E-linear equivalences F on every
test object. Their naturality is that of the encoded frame isomorphisms.
Restriction of the rational frame
along the coefficient inclusion gives c, while the integral frames give b.
In rational coordinates F is the rational frame map, composed with q_j and
with the inverse of the rationalized integral frame map. The regular-module
scalar-extension unit equation sends integral coordinates to the same vector in E.
The one-map mate equation for comapUpperStarIso identifies the adjoint of q_j with
the specified normalized sheet map, after the composition normalization by w j. This proves the
global equation; no matrix or open restriction
assertion is being assumed here. -/
theorem continuousFreeSheet_globalCoordinates
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (g : Y ⟶ X) (d : ℕ) (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hP : Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((upperStar (Profinite.continuousMapRingObj E) g).obj P))
    (hM : ∀ j, Mod.IsFree (condensedRingObj (integralCoeff l E) Y)
      ((upperStar (integralCoeff l E) (t j)).obj M)) :
    ∃ (r : ℕ) (n : Fin d → ℕ) (c : ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → E) ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj
          ((upperStar (Profinite.continuousMapRingObj E) g).obj P)))
      (b : ∀ j, ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin (n j) → continuousIntegers l E) ((upperStar (integralCoeff l E) (t j)).obj M))
      (F : ∀ (j : Fin d) (B : Y.ProEt),
        C(B.left, Fin (n j) → E) ≃ₗ[C(B.left, E)] C(B.left, Fin r → E)),
      (∀ (j : Fin d) (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin (n j) → E)),
        F j D (x.comp a.left.base.hom) = (F j B x).comp a.left.base.hom) ∧
      ∀ (j : Fin d) (B : Y.ProEt)
        (x : ((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.obj
          ((upperStar (integralCoeff l E) (t j)).obj M)).val.obj (op B)),
        c.sections B
          (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
            (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
              g (t j) (w j))).val.app (op B) x) =
          F j B (continuousIntegralVector (continuousIntegers l E) ((b j).sections B x)) := by
  classical
  obtain ⟨r, n, c, b, F, hF, hc⟩ := freeCoordinates l E Y
    ((upperStar (Profinite.continuousMapRingObj E) g).obj P) d
    (fun j ↦ (upperStar (integralCoeff l E) (t j)).obj M)
    (fun j ↦ sheetExtensionIso (integralScalarMap l E) P p M e g (t j) (w j)) hP hM
  refine ⟨r, n, c, b, F, hF, ?_⟩
  intro j B x
  rw [sheetEmbedding_unit]
  exact hc j B x

end AlgebraicGeometry.ProEtale.CondensedRing
