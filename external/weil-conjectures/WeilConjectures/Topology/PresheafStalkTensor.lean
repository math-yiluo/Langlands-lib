/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Tensor products of presheaf module stalks

Source: Stacks Project, Modules, Tag 01CB (lemma-stalk-tensor-product),
presheaf comparison in the omitted proof; compare the scalar-extension case in Sheaves, Tag 007K.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace Opposite

open scoped TensorProduct

universe u

namespace PresheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Taking the stalk of the sectionwise tensor product commutes with tensor products.
Source: Stacks Project, Modules, Tag 01CB (lemma-stalk-tensor-product), the presheaf
comparison in its omitted proof; compare Sheaves, Tag 007K for extension of scalars.
(blueprint: lem-pc-presheaf-module-stalk-tensor).

Proof:
1. The two germ maps give a balanced additive pairing on sections of each neighborhood.
   Lift it to the section tensor product. These additive maps commute with restriction
   by the tensor restriction formula and `germ_res_apply`; the colimit universal property
   gives the forward additive comparison `p` on the tensor-presheaf stalk.
2. Represent two module germs on a common neighborhood and take the germ of their tensor.
   Equality of germs is equality after restriction to a smaller neighborhood. Apply this
   separately to both factors, intersect the resulting neighborhoods, and use tensor
   restrictions to prove that the tensor germ is independent of the representatives.
3. This defines a pairing on the two stalks. To check additivity, represent the three
   vectors on a common neighborhood. To check linearity, also represent the scalar on
   that neighborhood and use `germ_smul`. Thus the pairing is bilinear over the stalk ring.
4. Its tensor lift `q` is inverse to `p`: on stage pure tensors this is the defining
   germ formula; in the other direction represent both factors on a common neighborhood.
   Tensor induction proves the inverse identities on all elements.
5. Because `q` is linear, its additive inverse `p` is linear as well. The bijective
   linear map gives the displayed module isomorphism and its germ formula. -/
theorem exists_stalk_tensor_iso {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})
    (x : X) (F G : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    ∃ e : ModuleCat.of (R.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) (F ⊗ G).presheaf x) ≅
      ModuleCat.of (R.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) F.presheaf x) ⊗
      ModuleCat.of (R.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) G.presheaf x),
      ∀ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) (t : G.obj (op U)),
        e.hom (TopCat.Presheaf.germ (F ⊗ G).presheaf U x hx
          (s ⊗ₜ[R.obj (op U)] t)) =
        TopCat.Presheaf.germ F.presheaf U x hx s ⊗ₜ[R.stalk x]
          TopCat.Presheaf.germ G.presheaf U x hx t := by
  classical
  let P := F ⊗ G
  let A := R.stalk x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) F.presheaf x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) G.presheaf x
  let T := TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) P.presheaf x
  let b₀ (U : Opens X) (hx : x ∈ U) : F.obj (op U) →+ G.obj (op U) →+ (M ⊗[A] N) :=
    { toFun := fun s ↦
        { toFun := fun t ↦ TopCat.Presheaf.germ F.presheaf U x hx s ⊗ₜ[A]
            TopCat.Presheaf.germ G.presheaf U x hx t
          map_zero' := by simp
          map_add' := by intro t t'; simp [TensorProduct.tmul_add] }
      map_zero' := by ext t; simp
      map_add' := by intro s s'; ext t; simp [TensorProduct.add_tmul] }
  have hb₀ (U : Opens X) (hx : x ∈ U) (a : R.obj (op U))
      (s : F.obj (op U)) (t : G.obj (op U)) :
      b₀ U hx (a • s) t = b₀ U hx s (a • t) := by
    change TopCat.Presheaf.germ F.presheaf U x hx (a • s) ⊗ₜ[A]
        TopCat.Presheaf.germ G.presheaf U x hx t =
      TopCat.Presheaf.germ F.presheaf U x hx s ⊗ₜ[A]
        TopCat.Presheaf.germ G.presheaf U x hx (a • t)
    rw [germ_smul F, germ_smul G, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  let p₀ (U : Opens X) (hx : x ∈ U) : P.obj (op U) →+ (M ⊗[A] N) :=
    TensorProduct.liftAddHom (b₀ U hx) (hb₀ U hx)
  have hp₀ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) (t : G.obj (op U)) :
      p₀ U hx (s ⊗ₜ[R.obj (op U)] t) =
        TopCat.Presheaf.germ F.presheaf U x hx s ⊗ₜ[A]
          TopCat.Presheaf.germ G.presheaf U x hx t := by
    rfl
  let c : Cocone ((OpenNhds.inclusion x).op ⋙ P.presheaf) :=
    { pt := AddCommGrpCat.of (M ⊗[A] N)
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom (p₀ i.unop.1 i.unop.2)
          naturality := by
            intro i j f
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro z
            change p₀ j.unop.1 j.unop.2 (P.map ((OpenNhds.inclusion x).op.map f) z) =
              p₀ i.unop.1 i.unop.2 z
            induction z using TensorProduct.inductionOn with
            | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
            | tmul s t =>
              erw [Monoidal.tensorObj_map_tmul, hp₀, hp₀]
              congr 1
              · exact TopCat.Presheaf.germ_res_apply' F.presheaf _ x _ s
              · exact TopCat.Presheaf.germ_res_apply' G.presheaf _ x _ t } }
  let p : T →+ (M ⊗[A] N) := (colimit.desc _ c).hom
  have hp (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) (t : G.obj (op U)) :
      p (TopCat.Presheaf.germ P.presheaf U x hx (s ⊗ₜ[R.obj (op U)] t)) =
        TopCat.Presheaf.germ F.presheaf U x hx s ⊗ₜ[A]
          TopCat.Presheaf.germ G.presheaf U x hx t := by
    change (colimit.ι _ (op ⟨U, hx⟩) ≫ colimit.desc _ c) (s ⊗ₜ[R.obj (op U)] t) = _
    rw [colimit.ι_desc]
    exact hp₀ U hx s t
  have hpairing : ∃ β : M →ₗ[A] N →ₗ[A] T,
      ∀ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) (t : G.obj (op U)),
        β (TopCat.Presheaf.germ F.presheaf U x hx s)
          (TopCat.Presheaf.germ G.presheaf U x hx t) =
        TopCat.Presheaf.germ P.presheaf U x hx (s ⊗ₜ[R.obj (op U)] t) := by
    have move {U V : Opens X} (hx : x ∈ V) (i : V ⟶ U)
        (s : F.obj (op U)) (t : G.obj (op U)) :
        TopCat.Presheaf.germ P.presheaf V x hx
          (F.map i.op s ⊗ₜ[R.obj (op V)] G.map i.op t) =
        TopCat.Presheaf.germ P.presheaf U x (i.le hx) (s ⊗ₜ[R.obj (op U)] t) := by
      change TopCat.Presheaf.germ P.presheaf V x hx (P.map i.op (s ⊗ₜ t)) = _
      change TopCat.Presheaf.germ P.presheaf V x hx
        (P.presheaf.map i.op (s ⊗ₜ[R.obj (op U)] t)) = _
      exact TopCat.Presheaf.germ_res_apply P.presheaf i x hx
        (s ⊗ₜ[R.obj (op U)] t)
    have uniq {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
        (s : F.obj (op U)) (t : G.obj (op U))
        (s' : F.obj (op V)) (t' : G.obj (op V))
        (hs : TopCat.Presheaf.germ F.presheaf U x hxU s =
          TopCat.Presheaf.germ F.presheaf V x hxV s')
        (ht : TopCat.Presheaf.germ G.presheaf U x hxU t =
          TopCat.Presheaf.germ G.presheaf V x hxV t') :
        TopCat.Presheaf.germ P.presheaf U x hxU (s ⊗ₜ[R.obj (op U)] t) =
          TopCat.Presheaf.germ P.presheaf V x hxV (s' ⊗ₜ[R.obj (op V)] t') := by
      obtain ⟨W, hxW, iWU, iWV, hs⟩ := TopCat.Presheaf.germ_eq F.presheaf x hxU hxV s s' hs
      obtain ⟨Z, hxZ, iZU, iZV, ht⟩ := TopCat.Presheaf.germ_eq G.presheaf x hxU hxV t t' ht
      have hx : x ∈ W ⊓ Z := ⟨hxW, hxZ⟩
      let iW : W ⊓ Z ⟶ W := homOfLE inf_le_left
      let iZ : W ⊓ Z ⟶ Z := homOfLE inf_le_right
      have hs' : F.map (iW ≫ iWU).op s = F.map (iW ≫ iWV).op s' := by
        change F.map iWU.op s = F.map iWV.op s' at hs
        have he := congrArg (F.map iW.op) hs
        rw [← map_comp_apply, ← map_comp_apply] at he
        exact he
      have ht' : G.map (iW ≫ iWU).op t = G.map (iW ≫ iWV).op t' := by
        change G.map iZU.op t = G.map iZV.op t' at ht
        have he := congrArg (G.map iZ.op) ht
        rw [← map_comp_apply, ← map_comp_apply] at he
        exact he
      rw [← move hx (iW ≫ iWU), ← move hx (iW ≫ iWV), hs', ht']
    have rep (m : M) (n : N) : ∃ (U : Opens X) (hx : x ∈ U)
        (s : F.obj (op U)) (t : G.obj (op U)),
        TopCat.Presheaf.germ F.presheaf U x hx s = m ∧
          TopCat.Presheaf.germ G.presheaf U x hx t = n := by
      obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      obtain ⟨V, hVU, hxV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq G.presheaf n hxU
      refine ⟨V, hxV, F.map (homOfLE hVU).op s, t, ?_, rfl⟩
      exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV s
    have ex (m : M) (n : N) : ∃ z : T, ∃ (U : Opens X) (hx : x ∈ U)
        (s : F.obj (op U)) (t : G.obj (op U)),
        TopCat.Presheaf.germ F.presheaf U x hx s = m ∧
          TopCat.Presheaf.germ G.presheaf U x hx t = n ∧
          TopCat.Presheaf.germ P.presheaf U x hx (s ⊗ₜ[R.obj (op U)] t) = z := by
      obtain ⟨U, hx, s, t, hs, ht⟩ := rep m n
      exact ⟨_, U, hx, s, t, hs, ht, rfl⟩
    let b (m : M) (n : N) : T := (ex m n).choose
    have hb (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) (t : G.obj (op U)) :
        b (TopCat.Presheaf.germ F.presheaf U x hx s)
          (TopCat.Presheaf.germ G.presheaf U x hx t) =
        TopCat.Presheaf.germ P.presheaf U x hx (s ⊗ₜ[R.obj (op U)] t) := by
      obtain ⟨V, hxV, s', t', hs, ht, hz⟩ := (ex
        (TopCat.Presheaf.germ F.presheaf U x hx s)
        (TopCat.Presheaf.germ G.presheaf U x hx t)).choose_spec
      exact hz.symm.trans (uniq hxV hx s' t' s t hs ht)
    have repAfter (U : Opens X) (hx : x ∈ U) (m : M) (n : N) :
        ∃ (V : Opens X) (hVU : V ≤ U) (hxV : x ∈ V)
          (s : F.obj (op V)) (t : G.obj (op V)),
          TopCat.Presheaf.germ F.presheaf V x hxV s = m ∧
            TopCat.Presheaf.germ G.presheaf V x hxV t = n := by
      obtain ⟨V, hVU, hxV, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq F.presheaf m hx
      obtain ⟨W, hWV, hxW, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq G.presheaf n hxV
      refine ⟨W, hWV.trans hVU, hxW, F.map (homOfLE hWV).op s, t, ?_, rfl⟩
      exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWV) x hxW s
    have baddM (m m' : M) (n : N) : b (m + m') n = b m n + b m' n := by
      obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      obtain ⟨V, hVU, hxV, s', t, hm, hn⟩ := repAfter U hxU m' n
      have hs := TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV s
      rw [← hs, ← hm, ← hn,
        ← (TopCat.Presheaf.germ F.presheaf V x hxV).hom.map_add, hb, hb, hb]
      simp only [TensorProduct.add_tmul, map_add]
    have baddN (m : M) (n n' : N) : b m (n + n') = b m n + b m n' := by
      obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf n
      obtain ⟨V, hVU, hxV, s, t', hm, hn⟩ := repAfter U hxU m n'
      have ht := TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE hVU) x hxV t
      rw [← ht, ← hm, ← hn,
        ← (TopCat.Presheaf.germ G.presheaf V x hxV).hom.map_add, hb, hb, hb]
      simp only [TensorProduct.tmul_add, map_add]
    have bsmulM (a : A) (m : M) (n : N) : b (a • m) n = a • b m n := by
      obtain ⟨U, hxU, a, rfl⟩ := R.exists_germ_eq a
      obtain ⟨V, hVU, hxV, s, t, hm, hn⟩ := repAfter U hxU m n
      have ha := R.germ_res_apply (homOfLE hVU) x hxV a
      rw [← hm, ← hn, ← ha, ← germ_smul F, hb, hb,
        ← germ_smul P, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul]
    have bsmulN (a : A) (m : M) (n : N) : b m (a • n) = a • b m n := by
      obtain ⟨U, hxU, a, rfl⟩ := R.exists_germ_eq a
      obtain ⟨V, hVU, hxV, s, t, hm, hn⟩ := repAfter U hxU m n
      have ha := R.germ_res_apply (homOfLE hVU) x hxV a
      rw [← hm, ← hn, ← ha, ← germ_smul G, hb, hb,
        ← germ_smul P, TensorProduct.tmul_smul]
    refine ⟨{
      toFun := fun m ↦
        { toFun := b m
          map_add' := baddN m
          map_smul' := fun a n ↦ bsmulN a m n }
      map_add' := by intro m m'; ext n; exact baddM m m' n
      map_smul' := by intro a m; ext n; exact bsmulM a m n }, hb⟩
  obtain ⟨β, hβ⟩ := hpairing
  let q : M ⊗[A] N →ₗ[A] T := TensorProduct.lift β
  have hqp : Function.LeftInverse q p := by
    intro z
    obtain ⟨U, hx, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s t => erw [hp]; exact hβ U hx s t
  have hpq : Function.LeftInverse p q := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul m n =>
      obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      obtain ⟨V, hVU, hxV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq G.presheaf n hxU
      rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV s]
      change p (β _ _) = _
      rw [hβ, hp]
  let ψ : T →ₗ[A] (M ⊗[A] N) :=
    { p with
      map_smul' := by
        intro a z
        apply hpq.injective
        change q (p (a • z)) = q (a • p z)
        rw [hqp, q.map_smul, hqp] }
  refine ⟨(LinearEquiv.ofBijective ψ ⟨hqp.injective, hpq.surjective⟩).toModuleIso, ?_⟩
  exact hp

end

end PresheafOfModules
