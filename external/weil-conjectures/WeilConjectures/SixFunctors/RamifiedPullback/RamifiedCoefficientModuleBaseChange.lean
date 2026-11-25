/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import Mathlib.RingTheory.Ideal.Maps

/-! # Scalar base change for a finite coefficient module

Source: Stacks Project, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
namespace CoefficientBC
universe v r w
variable {C : Type w} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

private abbrev Mods (A : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
private abbrev res {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
private abbrev ext {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) (M : Mods A) :=
  SheafOfModules.changeOfRings a M
private abbrev raw {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) (M : Mods A) :=
  SheafOfModules.changeOfRingsPresheaf a M
private abbrev eta {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) (M : Mods A) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app (raw a M)
private abbrev pure {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) (M : Mods A)
    (U : Cᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :=
  (eta a M).app U (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)

private theorem pure_natural {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) (M : Mods A)
    {U V : Cᵒᵖ} (f : U ⟶ V) (s : B.obj.obj U) (x : M.val.obj U) :
    (ext a M).val.map f (pure a M U s x) =
      pure a M V (B.obj.map f s) (M.val.map f x) := by
  let : Module (A.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.map f).hom).obj
          (M.val.obj V)) :=
    inferInstanceAs (Module (A.obj.obj V) (M.val.obj V))
  have h := PresheafOfModules.naturality_apply (eta a M) f
    (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)
  change (eta a M).app V ((raw a M).map f
    (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) =
      (ext a M).val.map f (pure a M U s x) at h
  rw [show (raw a M).map f
      (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) =
      B.obj.map f s ⊗ₜ[A.obj.obj V, (a.hom.app V).hom] M.val.map f x from
    Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap a M f) s x] at h
  exact h.symm

private theorem pure_smul {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) (M : Mods A)
    (U : Cᵒᵖ) (s t : B.obj.obj U) (x : M.val.obj U) :
    s • pure a M U t x = pure a M U (s * t) x := by
  exact ((eta a M).app U).hom.map_smul s
    (t ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) |>.symm

private def rawContract {R S B : Sheaf J CommRingCat.{r}} (c : R ⟶ S) (p : R ⟶ B)
    (N : Mods B) (U : Cᵒᵖ) (x : N.val.obj U) :
    (raw c ((res p).obj (SheafOfModules.unit _))).obj U ⟶
      (raw c ((res p).obj N)).obj U := by
  let := Module.compHom (B.obj.obj U) (p.hom.app U).hom
  let := Module.compHom (N.val.obj U) (p.hom.app U).hom
  let g : ModuleCat.of (R.obj.obj U) (B.obj.obj U) ⟶
      ModuleCat.of (R.obj.obj U) (N.val.obj U) := ModuleCat.ofHom
    { toFun := fun b ↦ b • x
      map_add' := fun b b' ↦ add_smul b b' x
      map_smul' := fun r b ↦ by
        change (p.hom.app U r * b) • x = p.hom.app U r • (b • x)
        exact mul_smul _ _ _ }
  exact (ModuleCat.extendScalars (c.hom.app U).hom).map g

private theorem rawContract_pure {R S B : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (N : Mods B) (U : Cᵒᵖ) (x : N.val.obj U)
    (s : S.obj.obj U) (b : B.obj.obj U) :
    let := Module.compHom (B.obj.obj U) (p.hom.app U).hom
    let := Module.compHom (N.val.obj U) (p.hom.app U).hom
    rawContract c p N U x (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] b) =
      s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] (b • x) := by
  unfold rawContract
  exact ModuleCat.ExtendScalars.map_tmul ..

private theorem kernel_pure {R S B T : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (q : S ⟶ T) (j : B ⟶ T)
    (e : ext c ((res p).obj (SheafOfModules.unit _)) ≅
      (res q).obj (SheafOfModules.unit _))
    (he : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (b : B.obj.obj U),
      e.hom.val.app U (pure c ((res p).obj (SheafOfModules.unit _)) U s b) =
        j.hom.app U b * q.hom.app U s)
    (N : Mods B) (U : Cᵒᵖ) (z : S.obj.obj U) (hz : q.hom.app U z = 0)
    (x : N.val.obj U) : pure c ((res p).obj N) U z x = 0 := by
  let K := (res p).obj (SheafOfModules.unit _)
  let P := (res p).obj N
  have hzK : pure c K U z (1 : B.obj.obj U) = 0 := by
    have hinj : Function.Injective (e.hom.val.app U) := by
      intro a b h
      have hh := congrArg (e.inv.val.app U) h
      have hi (y) : e.inv.val.app U (e.hom.val.app U y) = y :=
        congrArg (fun k ↦ k.val.app U y) e.hom_inv_id
      exact (hi a).symm.trans (hh.trans (hi b))
    apply hinj
    rw [he, hz, mul_zero, map_zero]
  let := Module.compHom (B.obj.obj U) (p.hom.app U).hom
  let a := (PresheafOfModules.toPresheaf _).map (eta c K)
  have : Presheaf.IsLocallyInjective J a := by
    change Presheaf.IsLocallyInjective J (toSheafify J (raw c K).presheaf)
    infer_instance
  have hcov := Presheaf.equalizerSieve_mem J a
    (z ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] (1 : B.obj.obj U)) 0
      (hzK.trans (map_zero _).symm)
  apply (ext c P).isSheaf.isSeparated _ _ hcov
  intro V f hf
  rw [map_zero]
  change (ext c P).val.map f.op (pure c P U z (show P.val.obj U from x)) = 0
  rw [pure_natural]
  let := Module.compHom (B.obj.obj (op V)) (p.hom.app (op V)).hom
  let := Module.compHom (N.val.obj (op V)) (p.hom.app (op V)).hom
  have hraw : (raw c K).map f.op
      (z ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] (1 : B.obj.obj U)) = 0 := by
    exact hf.trans (map_zero _)
  rw [show (raw c K).map f.op
      (z ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] (1 : B.obj.obj U)) =
      S.obj.map f.op z ⊗ₜ[R.obj.obj (op V), (c.hom.app (op V)).hom]
        (B.obj.map f.op 1) from
    Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c K f.op) z (1 : B.obj.obj U),
    map_one] at hraw
  have h := congrArg (rawContract c p N (op V) (N.val.map f.op x)) hraw
  rw [rawContract_pure, one_smul, map_zero] at h
  exact (congrArg ((eta c P).app (op V)) h).trans (map_zero _)

private theorem kernel_all {R S B T : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (q : S ⟶ T) (j : B ⟶ T)
    (e : ext c ((res p).obj (SheafOfModules.unit _)) ≅
      (res q).obj (SheafOfModules.unit _))
    (he : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (b : B.obj.obj U),
      e.hom.val.app U (pure c ((res p).obj (SheafOfModules.unit _)) U s b) =
        j.hom.app U b * q.hom.app U s)
    (N : Mods B) (U : Cᵒᵖ) (z : S.obj.obj U) (hz : q.hom.app U z = 0)
    (y : (ext c ((res p).obj N)).val.obj U) : z • y = 0 := by
  let P := (res p).obj N
  let a := (PresheafOfModules.toPresheaf _).map (eta c P)
  have : Presheaf.IsLocallySurjective J a := by
    change Presheaf.IsLocallySurjective J (toSheafify J (raw c P).presheaf)
    infer_instance
  apply (ext c P).isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J a y)
  rintro V f ⟨t, ht⟩
  change (ext c P).val.map f.op (z • y) = (ext c P).val.map f.op 0
  rw [PresheafOfModules.map_smul, map_zero]
  change S.obj.map f.op z •
    (show (ext c P).val.obj (op V) from (ext c P).val.map f.op y) = 0
  change (eta c P).app (op V) t = (ext c P).val.map f.op y at ht
  rw [← ht]
  have hz' : q.hom.app (op V) (S.obj.map f.op z) = 0 := by
    have h := ConcreteCategory.congr_hom (q.hom.naturality f.op) z
    exact h.trans ((congrArg (T.obj.map f.op) hz).trans (map_zero _))
  clear ht
  change (ModuleCat.extendScalars (c.hom.app (op V)).hom).obj (P.val.obj (op V)) at t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, smul_add, ha, hb, add_zero]
  | tmul s x =>
    change S.obj.map f.op z • pure c P (op V) s x = 0
    rw [pure_smul]
    exact kernel_pure c p q j e he N (op V) _
      (by rw [map_mul, hz', zero_mul]) x

private def quotientAction {S T M : Type*} [CommRing S] [CommRing T]
    [AddCommGroup M] [Module S M] (q : S →+* T) (hq : Function.Surjective q)
    (hz : ∀ s, q s = 0 → ∀ x : M, s • x = 0) : T →+* AddMonoid.End M :=
  q.liftOfSurjective hq ⟨Module.toAddMonoidEnd S M, fun s hs ↦ by
    apply AddMonoidHom.ext
    intro x
    exact hz s hs x⟩

@[instance_reducible] private def quotientModule {S T M : Type*} [CommRing S] [CommRing T]
    [AddCommGroup M] [Module S M] (q : S →+* T) (hq : Function.Surjective q)
    (hz : ∀ s, q s = 0 → ∀ x : M, s • x = 0) : Module T M where
  smul t x := quotientAction q hq hz t x
  one_smul x := congrArg (fun f : AddMonoid.End M ↦ f x) (map_one (quotientAction q hq hz))
  mul_smul a b x :=
    congrArg (fun f : AddMonoid.End M ↦ f x) (map_mul (quotientAction q hq hz) a b)
  smul_zero t := map_zero (quotientAction q hq hz t)
  smul_add t x y := map_add (quotientAction q hq hz t) x y
  zero_smul x :=
    congrArg (fun f : AddMonoid.End M ↦ f x) (map_zero (quotientAction q hq hz))
  add_smul a b x :=
    congrArg (fun f : AddMonoid.End M ↦ f x) (map_add (quotientAction q hq hz) a b)

private theorem quotientModule_smul {S T M : Type*} [CommRing S] [CommRing T]
    [AddCommGroup M] [Module S M] (q : S →+* T) (hq : Function.Surjective q)
    (hz : ∀ s, q s = 0 → ∀ x : M, s • x = 0) (s : S) (x : M) :
    @SMul.smul _ _ (quotientModule q hq hz).toSMul (q s) x = s • x := by
  exact congrArg (fun f : AddMonoid.End M ↦ f x)
    (q.liftOfSurjective_comp_apply hq ⟨Module.toAddMonoidEnd S M, _⟩ s)

private def descend {S T : Sheaf J CommRingCat.{r}} (q : S ⟶ T)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U)) (P : Mods S)
    (hz : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), q.hom.app U s = 0 →
      ∀ x : P.val.obj U, s • x = 0) : Mods T := by
  let (U : Cᵒᵖ) : Module
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj.obj U)
      (P.val.presheaf.obj U) := quotientModule
        (S := S.obj.obj U) (T := T.obj.obj U) (M := P.val.obj U)
        (q.hom.app U).hom (hq U) (hz U)
  refine ⟨PresheafOfModules.ofPresheaf P.val.presheaf ?_, P.isSheaf⟩
  intro U V f t x
  obtain ⟨s, rfl⟩ := hq U t
  change P.val.map f (@SMul.smul (T.obj.obj U) (P.val.obj U)
      (quotientModule (q.hom.app U).hom (hq U) (hz U)).toSMul (q.hom.app U s) x) =
    @SMul.smul (T.obj.obj V) (P.val.obj V)
      (quotientModule (q.hom.app V).hom (hq V) (hz V)).toSMul
        (T.obj.map f (q.hom.app U s)) (P.val.map f x)
  rw [quotientModule_smul]
  have hqf := ConcreteCategory.congr_hom (q.hom.naturality f) s
  change q.hom.app V (S.obj.map f s) = T.obj.map f (q.hom.app U s) at hqf
  rw [← hqf, quotientModule_smul]
  exact P.val.map_smul f s x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}] in
private theorem descend_smul {S T : Sheaf J CommRingCat.{r}} (q : S ⟶ T)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U)) (P : Mods S)
    (hz : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), q.hom.app U s = 0 →
      ∀ x : P.val.obj U, s • x = 0)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : P.val.obj U) :
    (q.hom.app U s) • (show (descend q hq P hz).val.obj U from x) = s • x := by
  exact quotientModule_smul (q.hom.app U).hom (hq U) (hz U) s x

variable [EssentiallySmall.{r} C]

private def adj {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B) :=
  CategoryTheory.CochainPullback.extensionAdjunction a

private theorem adj_unit {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
    (N : Mods A) (U : Cᵒᵖ) (x : N.val.obj U) :
    ((adj a).unit.app N).val.app U x = pure a N U 1 x :=
  (Classical.choose_spec
    (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique a)).1 N U x

private def lift {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
    {N : Mods A} {H : Mods B} (f : N ⟶ (res a).obj H) : ext a N ⟶ H :=
  ((adj a).homEquiv N H).symm f

private theorem lift_pure {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
    {N : Mods A} {H : Mods B} (f : N ⟶ (res a).obj H)
    (U : Cᵒᵖ) (s : B.obj.obj U) (x : N.val.obj U) :
    (lift a f).val.app U (pure a N U s x) = s • (show H.val.obj U from f.val.app U x) := by
  have h := ((adj a).homEquiv N H).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k ↦ k.val.app U x) h
  change (lift a f).val.app U (((adj a).unit.app N).val.app U x) = f.val.app U x at hh
  rw [adj_unit] at hh
  have ht := pure_smul a N U s 1 x
  rw [mul_one] at ht
  rw [← ht, map_smul, hh]

private theorem ext_hom_ext {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
    {N : Mods A} {H : Mods B} (f g : ext a N ⟶ H)
    (he : ∀ (U : Cᵒᵖ) (x : N.val.obj U),
      f.val.app U (pure a N U 1 x) = g.val.app U (pure a N U 1 x)) : f = g := by
  apply ((adj a).homEquiv N H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U x
  change f.val.app U (((adj a).unit.app N).val.app U x) =
    g.val.app U (((adj a).unit.app N).val.app U x)
  rw [adj_unit]
  exact he U x

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  [EssentiallySmall.{r} C] in
private theorem square_app {R S B T : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (q : S ⟶ T) (j : B ⟶ T)
    (hs : c ≫ q = p ≫ j) (U : Cᵒᵖ) (r : R.obj.obj U) :
    q.hom.app U (c.hom.app U r) = j.hom.app U (p.hom.app U r) :=
  congrArg (fun k ↦ k.hom.app U r) hs

private def forwardUnit {R S B T : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (q : S ⟶ T) (j : B ⟶ T)
    (hs : c ≫ q = p ≫ j) (N : Mods B) :
    (res p).obj N ⟶ (res c).obj ((res q).obj (ext j N)) := by
  let u : N ⟶ (res j).obj (ext j N) := (adj j).unit.app N
  refine ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj).map u.val) ?_⟩
  intro U r x
  change u.val.app U (p.hom.app U r • (show N.val.obj U from x)) =
    q.hom.app U (c.hom.app U r) • (show (ext j N).val.obj U from u.val.app U x)
  rw [square_app c p q j hs]
  exact (u.val.app U).hom.map_smul (p.hom.app U r) x

private def backwardUnit {R S B T : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (q : S ⟶ T) (j : B ⟶ T)
    (hs : c ≫ q = p ≫ j)
    (hp : ∀ U : Cᵒᵖ, Function.Surjective (p.hom.app U))
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U)) (N : Mods B)
    (hz : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), q.hom.app U s = 0 →
      ∀ x : (ext c ((res p).obj N)).val.obj U, s • x = 0) :
    N ⟶ (res j).obj (descend q hq (ext c ((res p).obj N)) hz) := by
  let u : (res p).obj N ⟶ (res c).obj (ext c ((res p).obj N)) :=
    (adj c).unit.app ((res p).obj N)
  refine ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj).map u.val) ?_⟩
  intro U b x
  obtain ⟨r, rfl⟩ := hp U b
  change u.val.app U (p.hom.app U r • (show N.val.obj U from x)) =
    j.hom.app U (p.hom.app U r) •
      (show (descend q hq (ext c ((res p).obj N)) hz).val.obj U from u.val.app U x)
  rw [← square_app c p q j hs, descend_smul]
  exact (u.val.app U).hom.map_smul r x

private def restore {S T : Sheaf J CommRingCat.{r}} (q : S ⟶ T)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U)) (P : Mods S)
    (hz : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), q.hom.app U s = 0 →
      ∀ x : P.val.obj U, s • x = 0) :
    (res q).obj (descend q hq P hz) ⟶ P := by
  refine ⟨PresheafOfModules.homMk (𝟙 P.val.presheaf) ?_⟩
  intro U s x
  exact descend_smul q hq P hz U s x

private def unrestrict {S T : Sheaf J CommRingCat.{r}} (q : S ⟶ T)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    {M H : Mods T} (f : (res q).obj M ⟶ (res q).obj H) : M ⟶ H := by
  refine ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj).map f.val) ?_⟩
  intro U t x
  obtain ⟨s, rfl⟩ := hq U t
  exact (f.val.app U).hom.map_smul s x

private theorem restricted_ext_hom_ext {B S T : Sheaf J CommRingCat.{r}}
    (j : B ⟶ T) (q : S ⟶ T)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    {N : Mods B} {H : Mods T}
    (f g : (res q).obj (ext j N) ⟶ (res q).obj H)
    (he : ∀ (U : Cᵒᵖ) (x : N.val.obj U),
      f.val.app U (pure j N U 1 x) = g.val.app U (pure j N U 1 x)) : f = g := by
  have h : unrestrict q hq f = unrestrict q hq g :=
    ext_hom_ext j _ _ he
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h

private theorem comparison_exists {R S B T : Sheaf J CommRingCat.{r}}
    (c : R ⟶ S) (p : R ⟶ B) (q : S ⟶ T) (j : B ⟶ T)
    (hs : c ≫ q = p ≫ j)
    (hp : ∀ U : Cᵒᵖ, Function.Surjective (p.hom.app U))
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U)) (N : Mods B)
    (hz : ∀ (U : Cᵒᵖ) (s : S.obj.obj U), q.hom.app U s = 0 →
      ∀ x : (ext c ((res p).obj N)).val.obj U, s • x = 0) :
    ∃ b : ext c ((res p).obj N) ≅ (res q).obj (ext j N),
      ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U),
        b.hom.val.app U (pure c ((res p).obj N) U s x) =
          pure j N U (q.hom.app U s) x := by
  let P := ext c ((res p).obj N)
  let Q := ext j N
  let D := descend q hq P hz
  let f : P ⟶ (res q).obj Q := lift c (forwardUnit c p q j hs N)
  let g : (res q).obj Q ⟶ P :=
    (res q).map (lift j (backwardUnit c p q j hs hp hq N hz)) ≫ restore q hq P hz
  have hf (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
      f.val.app U (pure c ((res p).obj N) U s x) =
        pure j N U (q.hom.app U s) x := by
    rw [show f = lift c (forwardUnit c p q j hs N) from rfl, lift_pure]
    change q.hom.app U s •
      (show Q.val.obj U from ((adj j).unit.app N).val.app U x) = _
    rw [adj_unit]
    simpa only [mul_one] using pure_smul j N U (q.hom.app U s) 1 x
  have hg (U : Cᵒᵖ) (x : N.val.obj U) :
      g.val.app U (pure j N U 1 x) = pure c ((res p).obj N) U 1 x := by
    change (lift j (backwardUnit c p q j hs hp hq N hz)).val.app U
      (pure j N U 1 x) = _
    rw [lift_pure, one_smul]
    exact adj_unit c ((res p).obj N) U x
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply ext_hom_ext c
    intro U x
    change g.val.app U (f.val.app U (pure c ((res p).obj N) U 1 x)) =
      pure c ((res p).obj N) U 1 x
    rw [hf, map_one, hg]
  · apply restricted_ext_hom_ext j q hq
    intro U x
    change f.val.app U (g.val.app U (pure j N U 1 x)) = pure j N U 1 x
    rw [hg, hf, map_one]

end CoefficientBC

attribute [local irreducible] HasDerivedCategory.standard scalarWitness

private def scalarIso {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) : (scalar.{t, u} c).obj M ≅
      SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} c M :=
  eqToIso ((scalarWitness.{t, u} c).choose_spec.choose M)

private theorem scalarIso_pure {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (scalarIso c M).inv.val.app U (CoefficientBC.pure c M U s x) =
      tensor.{t, u} c M U s x := by
  rfl

private theorem scalarIso_tensor {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (scalarIso c M).hom.val.app U (tensor.{t, u} c M U s x) =
      CoefficientBC.pure c M U s x := by
  rw [← scalarIso_pure]
  exact congrArg (fun f ↦ f.val.app U (CoefficientBC.pure c M U s x))
    (scalarIso c M).inv_hom_id

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem projection_surjective (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U) := by
  intro x
  obtain ⟨a, ha⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E W n U x
  refine ⟨(integralConstantToCompletionOfUniverses l E W).hom.app U a, ?_⟩
  exact (congrArg (fun h ↦ h.hom.app U a)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))).trans ha

/-- The coefficient base-change square acts on every finite module on one site.
Source: Stacks Project, Tags 03EK (section-tensor-product) and 03EL
(lemma-tensor-product-pullback), the balanced-tensor calculation in step 2 of
lem-weil-ramified-finite-module-comparison.
(blueprint: lem-weil-ramified-coefficient-module-base-change).

Proof: Write R,S for the two completed coefficient sheaves, B,T for the two
finite ones, and c:R→S, π:R→B, q:S→T, j:B→T for the square. The supplied
coefficientIso and coefficient_formula identify S tensor_R B with T by
s tensor b ↦ j(b)q(s). Give this tensor its commuting B-action on its second
factor, and give T the B-action through j. The coefficient formula proves
B-linearity on pure tensors: multiplying b by b0 multiplies the image by
j(b0). Tensor generation, followed by sheafification, proves B-linearity
on all sections. Its inverse is B-linear because it is inverse to a
B-linear bijection; both directions also retain their S-linearity.
For a B-module N, use the balanced tensor associator
S tensor_R Res(N) ≅ (S tensor_R B) tensor_B N, whose forward map sends
s tensor x to (s tensor 1) tensor x and inverse sends (s tensor b) tensor x
to s tensor bx. Tensor the supplied coefficient isomorphism with N. The
composite is S-linear, has an inverse given by that coefficient isomorphism's
inverse and the displayed associator, and sends s tensor x to q(s) tensor x.
These are maps of presheaves on local tensor representatives. Sheafification
and the tensor universal property descend them to module sheaves and verify
both inverse identities; the formula is preserved by the sheafification unit.
This uses neither a scheme morphism nor a reduction or pullback of N. It also
works when N=0 or the site is empty, and uses no flatness hypothesis. -/
theorem coefficientModuleBaseChange_exists (W : Scheme.{t})
    (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (data : Coefficients l E L ι e j W) (n : ℕ) :
    ∃ b : ∀ N : Mod.{t, u} (integralCoefficientCommRingSheaf l E W n),
      (scalar.{t, u} data.completedMap).obj
          ((SheafOfModules.restrictScalars.{max u (t + 1)}
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (completedIntegralCommRingProjectionUnrestricted l E W n))).obj N) ≅
        (SheafOfModules.restrictScalars.{max u (t + 1)}
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (completedIntegralCommRingProjectionUnrestricted l L W (index e n)))).obj
          ((scalar.{t, u} (ramifiedMap l E L W e n (j n))).obj N),
      ∀ (N : Mod.{t, u} (integralCoefficientCommRingSheaf l E W n))
        (U : W.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
        (x : N.val.obj U),
        (b N).hom.val.app U
          (tensor.{t, u} data.completedMap
            ((SheafOfModules.restrictScalars.{max u (t + 1)}
              ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
                (completedIntegralCommRingProjectionUnrestricted l E W n))).obj N) U s x) =
          @id (((SheafOfModules.restrictScalars.{max u (t + 1)}
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (completedIntegralCommRingProjectionUnrestricted l L W (index e n)))).obj
                ((scalar.{t, u} (ramifiedMap l E L W e n (j n))).obj N)).val.obj U)
            (tensor.{t, u} (ramifiedMap l E L W e n (j n)) N U
              ((completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s)
              x) := by
  let p := completedIntegralCommRingProjectionUnrestricted l E W n
  let q := completedIntegralCommRingProjectionUnrestricted l L W (index e n)
  let c := data.completedMap
  let jn := ramifiedMap l E L W e n (j n)
  let K := coefficientModule l E W n
  let ec : SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} c K ≅
      coefficientModule l L W (index e n) :=
    (scalarIso c K).symm ≪≫ data.coefficientIso n
  have hec (U : W.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
      (b : (integralCoefficientCommRingSheaf l E W n).obj.obj U) :
      ec.hom.val.app U (CoefficientBC.pure c K U s b) =
        jn.hom.app U b * q.hom.app U s := by
    change (data.coefficientIso n).hom.val.app U
      ((scalarIso c K).inv.val.app U (CoefficientBC.pure c K U s b)) = _
    rw [scalarIso_pure]
    exact data.coefficient_formula n U b s
  have hN (N : Mod.{t, u} (integralCoefficientCommRingSheaf l E W n)) :=
    CoefficientBC.comparison_exists c p q jn (data.ramified_projection n)
      (projection_surjective l E W n) (projection_surjective l L W (index e n)) N
      (CoefficientBC.kernel_all c p q jn ec hec N)
  choose b hb using hN
  refine ⟨fun N ↦ scalarIso c ((CoefficientBC.res p).obj N) ≪≫ b N ≪≫
    (CoefficientBC.res q).mapIso (scalarIso jn N).symm, ?_⟩
  intro N U s x
  change (scalarIso jn N).inv.val.app U
    ((b N).hom.val.app U
      ((scalarIso c ((CoefficientBC.res p).obj N)).hom.val.app U
        (tensor c ((CoefficientBC.res p).obj N) U s x))) = _
  rw [scalarIso_tensor, hb, scalarIso_pure]
  rfl

end WeilConjectures.RamifiedPullback
