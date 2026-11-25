/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower

/-! # Transporting the ordinary scalar tensor comparison

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace WeilConjectures

/-- A chosen presentation of ordinary scalar extension inherits the tensor-line comparison.
Source: Stacks, Modules on Sites, tensor products and scalar extension (03EK, 03EL).
(blueprint: lem-pur-ordinary-scalar-tensor-line-transport).
Proof: identify the chosen functor with the sheafified scalar tensor functor by
its specified object equalities. The hypothesis on maps makes this identification
natural. Apply the normalized binary scalar tensor comparison, tensor its second
factor with the specified line comparison, and conjugate by that natural
isomorphism. Naturality and the pure-tensor formula follow from the two
comparison formulas and cancellation of the conjugating isomorphism. The
scalar-extension sheafification universal property determines maps on pure
tensors, so it also gives uniqueness of the resulting natural isomorphism. -/
theorem ordinaryScalarTensorLineTransport
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v} RingCat.{max c v})]
    [HasSheafify J AddCommGrpCat.{max c v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v}]
    {R T : Sheaf J CommRingCat.{max c v}} (α : R ⟶ T)
    (F : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings α M)
    (hmF : ∀ {M M'} (f : M ⟶ M'), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom α M f ≫ eqToHom (hF M').symm)
    (t : ∀ (M : SheafOfModules.{max c v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (U : Cᵒᵖ), T.obj.obj U → M.val.obj U → (F.obj M).val.obj U)
    (ht : ∀ M U s x, t M U s x = (eqToHom (hF M).symm).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf α M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x)))
    (N : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (P : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (B : F.obj N ≅ P)
    (c : ∀ U : Cᵒᵖ, N.val.obj U → P.val.obj U)
    (hc : ∀ U y, B.hom.val.app U (t N U 1 y) = c U y) :
    ∃! b : SheafOfModules.siteSheafTensorRight N ⋙ F ≅
      F ⋙ SheafOfModules.siteSheafTensorRight P,
      ∀ M U s x y, (b.hom.app M).val.app U
          (t _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)) =
        SheafOfModules.siteSheafTensorTmul (F.obj M) P U
          (t M U s x)
          (c U y) := by
  classical
  let G := SheafOfModules.ScalarHomOrdinary.extensionFunctor.{c, v, max c v} α
  let e : F ≅ G := NatIso.ofComponents
    (fun M ↦ eqToIso (hF M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{c, v, max c v} α M)
    (by
      intro M M' f
      dsimp only [Iso.trans_hom, eqToIso.hom]
      rw [hmF]
      simp only [Category.assoc]
      rw [← Category.assoc (eqToHom (hF M').symm), eqToHom_trans]
      simp only [eqToHom_refl, Category.id_comp]
      apply (cancel_epi (eqToHom (hF M))).mpr
      change SheafOfModules.changeOfRingsHom α M f ≫
          (SheafOfModules.ScalarHomOrdinary.extensionIso α M').hom =
        (SheafOfModules.ScalarHomOrdinary.extensionIso α M).hom ≫ G.map f
      dsimp only [SheafOfModules.ScalarHomOrdinary.extensionIso, Functor.mapIso_hom,
        G, SheafOfModules.ScalarHomOrdinary.extensionFunctor,
        SheafOfModules.changeOfRingsHom, SheafOfModules.changeOfRingsHomOfUniverses]
      erw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)
  have he (M : SheafOfModules.{max c v} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) (s : T.obj.obj U)
      (x : M.val.obj U) :
      (e.hom.app M).val.app U (t M U s x) =
        SheafOfModules.scalarExtensionSection α M U s x := by
    rw [ht]
    change (SheafOfModules.ScalarHomOrdinary.extensionIso α M).hom.val.app U
      ((eqToHom (hF M)).val.app U ((eqToHom (hF M).symm).val.app U _)) = _
    have hc {A B : SheafOfModules.{max c v} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj T)} (h : A = B) (z : B.val.obj U) :
        (eqToHom h).val.app U ((eqToHom h.symm).val.app U z) = z := by
      cases h
      rfl
    rw [hc]
    let adj := PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)
    have hn := adj.unit.naturality
      (SheafOfModules.ScalarHomOrdinary.extensionPresheafIso α M).hom
    exact (congrArg (fun f ↦ f.app U
      (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x)) hn).symm
  let B' : G.obj N ≅ P := (e.app N).symm ≪≫ B
  obtain ⟨k⟩ := SheafOfModules.exists_scalarExtensionTensorCore R T α
  let bG : SheafOfModules.siteSheafTensorRight N ⋙ G ≅
      G ⋙ SheafOfModules.siteSheafTensorRight P :=
    NatIso.ofComponents
      (fun M ↦ k.tensorComparison M N ≪≫
        SheafOfModules.tensorSecondIso.{c, v, max c v} (G.obj M) B')
      (by
        intro M M' f
        dsimp only [Iso.trans_hom, SheafOfModules.tensorSecondIso_hom, Functor.comp_map]
        change (SheafOfModules.changeOfRingsHomOfUniverses α _
          ((SheafOfModules.siteSheafTensorRight N).map f) ≫
            (k.tensorComparison M' N).hom ≫ _) = _
        rw [← Category.assoc, k.first_natural f N]
        dsimp only [G, SheafOfModules.ScalarHomOrdinary.extensionFunctor]
        simp only [Category.assoc]
        exact congrArg (fun h ↦ (k.tensorComparison M N).hom ≫ h)
            (SheafOfModules.siteSheafTensorSecondMap_naturality
              (SheafOfModules.changeOfRingsHomOfUniverses α M f) B'.hom))
  let b : SheafOfModules.siteSheafTensorRight N ⋙ F ≅
      F ⋙ SheafOfModules.siteSheafTensorRight P :=
    Functor.isoWhiskerLeft _ e ≪≫ bG ≪≫ Functor.isoWhiskerRight e.symm _
  have hb : ∀ M U s x y, (b.hom.app M).val.app U
          (t _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)) =
        SheafOfModules.siteSheafTensorTmul (F.obj M) P U
          (t M U s x)
          (c U y) := by
    intro M U s x y
    change ((SheafOfModules.siteSheafTensorRight P).map (e.inv.app M)).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap (G.obj M) B'.hom).val.app U
        ((k.tensorComparison M N).hom.val.app U
          ((e.hom.app _).val.app U _))) = _
    rw [he ((SheafOfModules.siteSheafTensorRight N).obj M) U s
      (SheafOfModules.siteSheafTensorTmul M N U x y)]
    rw [k.tensor_tmul M N U s x y]
    change ((SheafOfModules.siteSheafTensorRight P).map (e.inv.app M)).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap (G.obj M) B'.hom).val.app U
        (SheafOfModules.siteSheafTensorTmul (G.obj M) (G.obj N) U
          (SheafOfModules.scalarExtensionSection α M U s x)
          (SheafOfModules.scalarExtensionSection α N U 1 y))) = _
    rw [SheafOfModules.scalarTensor_second_tmul (G.obj M) B'.hom,
      SheafOfModules.scalarTensor_first_tmul (e.inv.app M) P]
    have hleft := congrArg (fun z ↦ (e.inv.app M).val.app U z) (he M U s x)
    have hinv : (e.inv.app M).val.app U
        ((e.hom.app M).val.app U (t M U s x)) =
      t M U s x := by
      exact congrArg (fun f ↦ f.val.app U (t M U s x))
        (e.app M).hom_inv_id
    rw [← hleft, hinv]
    apply congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul _ _ U
      (t M U s x) z)
    change B.hom.val.app U
      ((e.inv.app N).val.app U (SheafOfModules.scalarExtensionSection α N U 1 y)) = _
    rw [← he N U 1 y]
    have hcancel := congrArg (fun f ↦ f.val.app U (t N U 1 y))
      (e.app N).hom_inv_id
    change (e.inv.app N).val.app U ((e.hom.app N).val.app U _) =
      t N U 1 y at hcancel
    rw [hcancel]
    exact hc U y
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (e.app ((SheafOfModules.siteSheafTensorRight N).obj M)).inv).mp
  apply SheafOfModules.scalarExtension_tensor_hom_ext α M N
  intro U s x y
  have hey := he ((SheafOfModules.siteSheafTensorRight N).obj M) U s
    (SheafOfModules.siteSheafTensorTmul M N U x y)
  have hcancel := congrArg (fun f ↦ f.val.app U (t _ U s
    (SheafOfModules.siteSheafTensorTmul M N U x y)))
      (e.app ((SheafOfModules.siteSheafTensorRight N).obj M)).hom_inv_id
  change (e.inv.app _).val.app U ((e.hom.app _).val.app U _) =
    t _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)
      at hcancel
  change (b'.hom.app M).val.app U ((e.inv.app _).val.app U _) =
    (b.hom.app M).val.app U ((e.inv.app _).val.app U _)
  rw [← hey, hcancel, hb', hb]

end WeilConjectures
