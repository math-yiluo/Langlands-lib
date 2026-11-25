/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
import WeilConjectures.Topology.SheafOfModulesFromBasis
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Extending modules on an indexed basis

Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-indexed-basis)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

private theorem indexedModule_hom_ext
    {X : TopCat.{u}} {I : Type u} {U : I → Opens X} (hB : IsBasis (Set.range U))
    {R : TopCat.Sheaf RingCat.{u} X} {E G : SheafOfModules.{u} R}
    {f g : E ⟶ G}
    (h : ∀ (i : I) (t : E.val.obj (op (U i))),
      f.val.app (op (U i)) t = g.val.app (op (U i)) t) : f = g := by
  apply (SheafOfModules.toSheaf R).map_injective
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext (B := U) E.val.presheaf
    ((SheafOfModules.toSheaf R).obj G) hB
  intro i
  ext t
  exact h i t

private theorem indexedModule_extend_hom
    {X : TopCat.{u}} {I : Type u} {U : I → Opens X} (hB : IsBasis (Set.range U))
    {R : TopCat.Sheaf RingCat.{u} X} (E G : SheafOfModules.{u} R)
    (α : ∀ i : I, E.val.obj (op (U i)) →ₗ[R.obj.obj (op (U i))]
      G.val.obj (op (U i)))
    (hα : ∀ (i j : I) (h : U j ≤ U i) (t : E.val.obj (op (U i))),
      α j (E.val.map (homOfLE h).op t) = G.val.map (homOfLE h).op (α i t)) :
    ∃! f : E ⟶ G, ∀ (i : I) (t : E.val.obj (op (U i))),
      f.val.app (op (U i)) t = α i t := by
  classical
  let β : (inducedFunctor U).op ⋙ E.val.presheaf ⟶
      (inducedFunctor U).op ⋙ G.val.presheaf :=
    { app := fun k => AddCommGrpCat.ofHom (α k.unop).toAddMonoidHom
      naturality := by
        intro k l f
        ext t
        exact hα k.unop l.unop f.unop.hom.le t }
  let γ : E.val.presheaf ⟶ G.val.presheaf := TopCat.Sheaf.restrictHomEquivHom E.val.presheaf
    ((SheafOfModules.toSheaf R).obj G) hB β
  have hγ (i : I) (t : E.val.obj (op (U i))) : γ.app (op (U i)) t = α i t := by
    change (TopCat.Sheaf.restrictHomEquivHom E.val.presheaf
      ((SheafOfModules.toSheaf R).obj G) hB β).app (op (U i)) t = _
    rw [TopCat.Sheaf.extend_hom_app]
    rfl
  have hlin (W : (Opens X)ᵒᵖ) (a : R.obj.obj W) (t : E.val.obj W) :
      γ.app W (a • t) = a • (γ.app W t : G.val.obj W) := by
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf R).obj G) W.unop
    intro x hx
    obtain ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, hxU, hUW⟩ := hB.exists_subset_of_mem_open hx W.unop.isOpen
    change TopCat.Presheaf.germ G.val.presheaf W.unop x hx (γ.app W (a • t)) =
      TopCat.Presheaf.germ G.val.presheaf W.unop x hx (a • γ.app W t)
    rw [← TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hUW) x hxU,
      ← TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hUW) x hxU]
    congr 1
    have hn (s : E.val.obj W) :
        G.val.map (homOfLE hUW).op (γ.app W s) =
          γ.app (op (U i)) (E.val.map (homOfLE hUW).op s) :=
      (CategoryTheory.congr_fun (γ.naturality (homOfLE hUW).op) s).symm
    change G.val.map (homOfLE hUW).op (γ.app W (a • t)) =
      G.val.map (homOfLE hUW).op (a • γ.app W t)
    rw [hn, E.val.map_smul, G.val.map_smul, hn, hγ i, hγ i, map_smul]
  let f : E ⟶ G := ⟨PresheafOfModules.homMk γ hlin⟩
  refine ⟨f, hγ, ?_⟩
  intro g hg
  exact indexedModule_hom_ext hB (fun i t => (hg i t).trans (hγ i t).symm)

private theorem indexedModule_isIso
    {X : TopCat.{u}} {I : Type u} {U : I → Opens X} (hB : IsBasis (Set.range U))
    {R : TopCat.Sheaf RingCat.{u} X} {E G : SheafOfModules.{u} R}
    (f : E ⟶ G) (hf : ∀ i : I, Function.Bijective (f.val.app (op (U i)))) :
    IsIso f := by
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := U) hB
    intro i
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact hf i
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)


set_option backward.isDefEq.respectTransparency false in
/-- The basis-extension theorem with repeated representatives of the same open allowed.
Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-indexed-basis)

Proof:
1. Set B=range U and choose one index c(V) for each V in B. Give V the module Q(c(V)),
   transported along U(c(V))=V. Restriction is r between the chosen indices. The identity,
   composition and scalar laws descend to this presheaf of modules.
2. For any i,j with U i=U j, restriction in each direction is inverse to the other:
   apply composition and then identity. These inverse maps identify all representatives.
   In particular the chosen representative of an intersection identifies with cap i j.
3. The finite refinement hypothesis descends to B: index a covering by its members,
   choose an index for each, apply hrefine and take the displayed finite basis opens.
   Transport each compatible finite family to the chosen representatives. Composition
   and the inverse identifications from step 2 translate overlap equality into hglue.
   Transport its unique glued element back to obtain finite unique gluing on B.
4. Apply exists_sheafOfModules_from_basis. For each original i compose its chosen-basis
   section equivalence with the inverse representative identification of step 2 to obtain
   iota i. Composition proves its restriction law.
5. A compatible linear family psi restricts to the chosen representatives. Apply the
   basis-extension universal property to obtain its unique morphism. Composition extends
   its section formula to every original index, and uniqueness on chosen indices proves
   uniqueness on all indices. If every psi i is bijective, so is every chosen map, and
   the basis-extension isomorphism criterion applies. Empty covers are included in hglue,
   so this construction also applies to the empty space and empty basis. -/
theorem exists_sheafOfModules_from_indexed_basis
    (X : TopCat.{u}) (I : Type u) (U : I → Opens X)
    (hB : IsBasis (Set.range U))
    (cap : I → I → I) (hcap : ∀ i j, U (cap i j) = U i ⊓ U j)
    (hrefine : ∀ (i : I) (J : Type u) (V : J → I),
      (⨆ j, U (V j)) = U i →
      ∃ (n : ℕ) (W : Fin n → I), (⨆ k, U (W k)) = U i ∧
        ∀ k, ∃ j, U (W k) ≤ U (V j))
    (R : TopCat.Sheaf RingCat.{u} X)
    (Q : ∀ i : I, ModuleCat.{u} (R.obj.obj (op (U i))))
    (r : ∀ (i j : I), U j ≤ U i → Q i →+ Q j)
    (rid : ∀ (i : I) (s : Q i), r i i le_rfl s = s)
    (rcomp : ∀ (i j k : I) (hji : U j ≤ U i) (hkj : U k ≤ U j) (s : Q i),
      r j k hkj (r i j hji s) = r i k (hkj.trans hji) s)
    (rsmul : ∀ (i j : I) (h : U j ≤ U i) (a : R.obj.obj (op (U i))) (s : Q i),
      r i j h (a • s) = R.obj.map (homOfLE h).op a • r i j h s)
    (hglue : ∀ (i : I) (n : ℕ) (V : Fin n → I) (hV : ∀ j, U (V j) ≤ U i),
      (⨆ j, U (V j)) = U i → ∀ s : ∀ j, Q (V j),
      (∀ j k,
        r (V j) (cap (V j) (V k)) (by rw [hcap]; exact inf_le_left) (s j) =
        r (V k) (cap (V j) (V k)) (by rw [hcap]; exact inf_le_right) (s k)) →
      ∃! t : Q i, ∀ j, r i (V j) (hV j) t = s j) :
    ∃ (E : SheafOfModules.{u} R)
      (iota : ∀ i : I, E.val.obj (op (U i)) ≃ₗ[R.obj.obj (op (U i))] Q i),
      (∀ (i j : I) (h : U j ≤ U i) (s : E.val.obj (op (U i))),
        iota j (E.val.map (homOfLE h).op s) = r i j h (iota i s)) ∧
      (∀ (G : SheafOfModules.{u} R)
        (psi : ∀ i : I, Q i →ₗ[R.obj.obj (op (U i))] G.val.obj (op (U i))),
        (∀ (i j : I) (h : U j ≤ U i) (s : Q i),
          psi j (r i j h s) = G.val.map (homOfLE h).op (psi i s)) →
        (∃! phi : E ⟶ G, ∀ (i : I) (s : E.val.obj (op (U i))),
          phi.val.app (op (U i)) s = psi i (iota i s)) ∧
        (∀ (phi : E ⟶ G),
          (∀ (i : I) (s : E.val.obj (op (U i))),
            phi.val.app (op (U i)) s = psi i (iota i s)) →
          (∀ i : I, Function.Bijective (psi i)) → IsIso phi)) := by
  classical
  have hex : ∃ (E : SheafOfModules.{u} R)
      (iota : ∀ i : I, E.val.obj (op (U i)) ≃ₗ[R.obj.obj (op (U i))] Q i),
      ∀ (i j : I) (h : U j ≤ U i) (s : E.val.obj (op (U i))),
        iota j (E.val.map (homOfLE h).op s) = r i j h (iota i s) := by
    -- Restrict scalars along equalities to keep the section carriers unchanged.
    let B : Set (Opens X) := Set.range U
    let c : B → I := fun V => V.property.choose
    have hc (V : B) : U (c V) = V.val := V.property.choose_spec
    let F (V : B) : ModuleCat.{u} (R.obj.obj (op V.val)) :=
      (ModuleCat.restrictScalars
        (R.obj.map (eqToHom (congrArg op (hc V).symm))).hom).obj (Q (c V))
    let rb (V W : B) (h : W.val ≤ V.val) : F V →+ F W :=
      r (c V) (c W) (by simpa only [hc] using h)
    have hcapB (V W : B) : V.val ⊓ W.val ∈ B := by
      exact ⟨cap (c V) (c W), by rw [hcap, hc, hc]⟩
    have hrid (V : B) (s : F V) : rb V V le_rfl s = s := rid (c V) s
    have hrcomp (V W Z : B) (hWV : W.val ≤ V.val) (hZW : Z.val ≤ W.val)
        (s : F V) : rb W Z hZW (rb V W hWV s) = rb V Z (hZW.trans hWV) s :=
      rcomp (c V) (c W) (c Z) _ _ s
    have hrsmul (V W : B) (h : W.val ≤ V.val)
        (a : R.obj.obj (op V.val)) (s : F V) :
        rb V W h (a • s) = R.obj.map (homOfLE h).op a • rb V W h s := by
      change r (c V) (c W) _
          (R.obj.map (eqToHom (congrArg op (hc V).symm)) a • s) =
        R.obj.map (eqToHom (congrArg op (hc W).symm))
          (R.obj.map (homOfLE h).op a) • r (c V) (c W) _ s
      rw [rsmul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← R.obj.map_comp, ← R.obj.map_comp]
      rfl
    have hrefB (V : B) (C : Set B) (_hC : ∀ W ∈ C, W.val ≤ V.val)
        (hcov : (⨆ W ∈ C, W.val) = V.val) :
        ∃ (n : ℕ) (W : Fin n → B), (⨆ k, (W k).val) = V.val ∧
          ∀ k, ∃ Z ∈ C, (W k).val ≤ Z.val := by
      have hcov' : (⨆ Z : C, U (c Z.val)) = U (c V) := by
        simpa only [hc, iSup_subtype] using hcov
      obtain ⟨n, W, hW, hWC⟩ := hrefine (c V) C (fun Z => c Z.val) hcov'
      refine ⟨n, fun k => ⟨U (W k), ⟨W k, rfl⟩⟩, ?_, ?_⟩
      · simpa only [hc] using hW
      · intro k
        obtain ⟨Z, hZ⟩ := hWC k
        exact ⟨Z.val, Z.property, by simpa only [hc] using hZ⟩
    have hglueB (V : B) (n : ℕ) (W : Fin n → B)
        (hW : ∀ j, (W j).val ≤ V.val) (hcov : (⨆ j, (W j).val) = V.val)
        (s : ∀ j, F (W j))
        (hs : ∀ j k,
          rb (W j) ⟨(W j).val ⊓ (W k).val, hcapB (W j) (W k)⟩ inf_le_left (s j) =
          rb (W k) ⟨(W j).val ⊓ (W k).val, hcapB (W j) (W k)⟩ inf_le_right (s k)) :
        ∃! t : F V, ∀ j, rb V (W j) (hW j) t = s j := by
      apply hglue (c V) n (fun j => c (W j))
        (fun j => by simpa only [hc] using hW j)
        (by simpa only [hc] using hcov) s
      intro j k
      let Z : B := ⟨(W j).val ⊓ (W k).val, hcapB (W j) (W k)⟩
      have hz : U (cap (c (W j)) (c (W k))) ≤ U (c Z) := by
        rw [hcap, hc, hc, hc]
      -- Move the equality on the chosen intersection to the original cap index.
      have hh := congrArg (r (c Z) (cap (c (W j)) (c (W k))) hz) (hs j k)
      change r (c Z) _ hz (r _ _ _ (s j)) = r (c Z) _ hz (r _ _ _ (s k)) at hh
      simpa only [rcomp] using hh
    obtain ⟨E, iota, hi, _⟩ := exists_sheafOfModules_from_basis
      X B hB hcapB hrefB R F rb hrid hrcomp hrsmul hglueB
    let b (i : I) : B := ⟨U i, ⟨i, rfl⟩⟩
    let e (i : I) : F (b i) ≃ₗ[R.obj.obj (op (U i))] Q i :=
      { toFun := r (c (b i)) i (by rw [hc])
        invFun := r i (c (b i)) (by rw [hc])
        left_inv := by intro s; rw [rcomp, rid]
        right_inv := by intro s; rw [rcomp, rid]
        map_add' := map_add _
        map_smul' := by
          intro a s
          change r (c (b i)) i _
            (R.obj.map (eqToHom (congrArg op (hc (b i)).symm)) a • s) =
            a • r (c (b i)) i _ s
          rw [rsmul]
          congr 1
          rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp]
          have hh : eqToHom (congrArg op (hc (b i)).symm) ≫
              (homOfLE (show U i ≤ U (c (b i)) by rw [hc])).op =
              𝟙 (op (U i)) := Subsingleton.elim _ _
          rw [hh, R.obj.map_id]
          rfl }
    refine ⟨E, fun i => (iota (b i)).trans (e i), ?_⟩
    intro i j h s
    change r (c (b j)) j _ (iota (b j) (E.val.map (homOfLE h).op s)) =
      r i j h (r (c (b i)) i _ (iota (b i) s))
    rw [hi (b i) (b j) h]
    change r (c (b j)) j _ (r (c (b i)) (c (b j)) _ (iota (b i) s)) = _
    rw [rcomp, rcomp]
  -- Extend linear maps on the indexed basis directly, without choosing representatives.
  obtain ⟨E, iota, hi⟩ := hex
  refine ⟨E, iota, hi, ?_⟩
  intro G psi hpsi
  have hext : ∃! phi : E ⟶ G, ∀ (i : I) (s : E.val.obj (op (U i))),
      phi.val.app (op (U i)) s = psi i (iota i s) := by
    apply indexedModule_extend_hom hB E G
      (fun i => (psi i).comp (iota i).toLinearMap)
    intro i j h s
    change psi j (iota j (E.val.map (homOfLE h).op s)) = _
    rw [hi, hpsi]
    rfl
  refine ⟨hext, ?_⟩
  intro phi hphi hbij
  apply indexedModule_isIso hB phi
  intro i
  have hh : (fun s => phi.val.app (op (U i)) s) = fun s => psi i (iota i s) :=
    funext (hphi i)
  convert (hbij i).comp (iota i).bijective using 1
  exact hh

end TopologicalSpace.Opens
