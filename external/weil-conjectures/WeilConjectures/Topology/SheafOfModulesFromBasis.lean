/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Topology.BasisSheafCofinalCoverings
import WeilConjectures.Topology.SheafOnBasisExtends

/-!
# Extending modules from a basis

Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U
(blueprint: lem-weil-pbc-sheaf-of-modules-from-basis).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- Compatible module structures on basis sections extend to an abelian sheaf.
Source: Stacks Project, Sheaves on Spaces, Section 009H, Lemma 009T.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-basis).

Proof:
For a basis open U transport its scalar action through the additive equivalence j U.
The restriction compatibility of j and the semilinearity of r make these actions natural
on the basis. Form the presheaf of sets P(W) = R(W) × A(W). The basis actions define
compatible maps from P into the underlying sheaf of sets of A. Extend them uniquely
using `lem-weil-pbc-sheaf-morphism-on-basis`. Naturality gives semilinearity of every
restriction. For each module axiom, the two sides are natural transformations into the
underlying sheaf of sets of A, with domain the appropriate product of ring and abelian
presheaves. Their basis components agree by the module axioms of F, so the transformations
agree globally by uniqueness of extension. Thus each A(W) is a module over R(W), its
restrictions are semilinear, and its underlying abelian presheaf remains A. This defines
E via PresheafOfModules.ofPresheaf and the sheaf condition of A. The additive equivalences
j become linear equivalences by the defining formula for the transported basis action;
compatibility with restrictions is unchanged. The assertion uses no covering or stalk
hypotheses and proves only the scalar-action step of the basis-extension construction. -/
private theorem exists_module_structure_on_basis_extension
    (X : TopCat.{u}) (B : Set (Opens X)) (hB : IsBasis B)
    (R : TopCat.Sheaf RingCat.{u} X)
    (F : ∀ U : B, ModuleCat.{u} (R.obj.obj (op U.val)))
    (r : ∀ (U V : B), V.val ≤ U.val → F U →+ F V)
    (rsmul : ∀ (U V : B) (h : V.val ≤ U.val) (a : R.obj.obj (op U.val)) (s : F U),
      r U V h (a • s) = R.obj.map (homOfLE h).op a • r U V h s)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X)
    (j : ∀ U : B, A.obj.obj (op U.val) ≃+ F U)
    (hj : ∀ (U V : B) (h : V.val ≤ U.val) (t : A.obj.obj (op U.val)),
      j V (A.obj.map (homOfLE h).op t) = r U V h (j U t)) :
    ∃ (E : SheafOfModules.{u} R)
      (ι : ∀ U : B, E.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U),
      ∀ (U V : B) (h : V.val ≤ U.val) (t : E.val.obj (op U.val)),
        ι V (E.val.map (homOfLE h).op t) = r U V h (ι U t) := by
  classical
  let P : (Opens X)ᵒᵖ ⥤ Type u :=
    { obj := fun W => R.obj.obj W × A.obj.obj W
      map := fun f => ↾fun s => (R.obj.map f s.1, A.obj.map f s.2)
      map_id := by
        intro W
        ext s <;> simp
      map_comp := by
        intro U V W f g
        ext s <;> simp }
  let Atypes : TopCat.Sheaf (Type u) X :=
    (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj A
  let β : (inducedFunctor (fun U : B => U.val)).op ⋙ P ⟶
      (inducedFunctor (fun U : B => U.val)).op ⋙ Atypes.obj :=
    { app := fun U => ↾fun s => (j U.unop).symm (s.1 • j U.unop s.2)
      naturality := by
        intro U V f
        ext s
        apply (j V.unop).injective
        change j V.unop ((j V.unop).symm (_ • j V.unop _)) =
          j V.unop (A.obj.map f.unop.hom.op ((j U.unop).symm (_ • j U.unop _)))
        change (j V.unop) ((j V.unop).symm
            (R.obj.map (homOfLE f.unop.hom.le).op s.1 •
              j V.unop (A.obj.map (homOfLE f.unop.hom.le).op s.2))) =
          j V.unop (A.obj.map (homOfLE f.unop.hom.le).op
            ((j U.unop).symm (s.1 • j U.unop s.2)))
        simp only [AddEquiv.apply_symm_apply, hj, rsmul] }
  have hb : IsBasis (Set.range (fun U : B => U.val)) := by
    simpa only [Subtype.range_coe] using hB
  let μ : P ⟶ A.obj ⋙ forget AddCommGrpCat :=
    TopCat.Sheaf.restrictHomEquivHom P Atypes hb β
  have hμ (U : B) (a : R.obj.obj (op U.val)) (t : A.obj.obj (op U.val)) :
      μ.app (op U.val) (a, t) = (j U).symm (a • j U t) := by
    change (TopCat.Sheaf.restrictHomEquivHom P Atypes hb β).app (op U.val) (a, t) = _
    rw [TopCat.Sheaf.extend_hom_app]
    rfl
  have hres {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (a : R.obj.obj U)
      (t : A.obj.obj U) :
      A.obj.map f (μ.app U (a, t)) = μ.app V (R.obj.map f a, A.obj.map f t) :=
    by
    have h := congrArg (fun g : P.obj U ⟶ ↑(A.obj.obj V) =>
      g (show P.obj U from (a, t))) (μ.naturality f)
    exact h.symm
  have heq (W : (Opens X)ᵒᵖ) (s t : A.obj.obj W)
      (h : ∀ (U : B) (hUW : U.val ≤ W.unop),
        A.obj.map (homOfLE hUW).op s = A.obj.map (homOfLE hUW).op t) : s = t := by
    apply TopCat.Presheaf.section_ext A W.unop
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := hB.exists_subset_of_mem_open hx W.unop.isOpen
    rw [← TopCat.Presheaf.germ_res_apply A.obj (homOfLE hUW) x hxU,
      ← TopCat.Presheaf.germ_res_apply A.obj (homOfLE hUW) x hxU, h ⟨U, hU⟩ hUW]
  let act (W : (Opens X)ᵒᵖ) (a : R.obj.obj W) (t : A.obj.obj W) : A.obj.obj W :=
    μ.app W (a, t)
  have hact (U : B) (a : R.obj.obj (op U.val)) (t : A.obj.obj (op U.val)) :
      j U (act (op U.val) a t) = a • j U t := by
    dsimp only [act]
    rw [hμ, AddEquiv.apply_symm_apply]
  have hn {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (a : R.obj.obj U) (t : A.obj.obj U) :
      A.obj.map f (act U a t) = act V (R.obj.map f a) (A.obj.map f t) := hres f a t
  let inst (W : (Opens X)ᵒᵖ) : Module (R.obj.obj W) (A.obj.obj W) :=
    { smul := act W
      one_smul := by
        intro t
        change act W 1 t = t
        apply heq W
        intro U hUW
        apply (j U).injective
        simp only [hn, hact, map_one, one_smul]
      mul_smul := by
        intro a b t
        change act W (a * b) t = act W a (act W b t)
        apply heq W
        intro U hUW
        apply (j U).injective
        simp only [hn, hact, map_mul, mul_smul]
      smul_zero := by
        intro a
        change act W a 0 = 0
        apply heq W
        intro U hUW
        apply (j U).injective
        simp only [hn, hact, map_zero, smul_zero]
      smul_add := by
        intro a t s
        change act W a (t + s) = act W a t + act W a s
        apply heq W
        intro U hUW
        apply (j U).injective
        simp only [hn, hact, map_add, smul_add]
      add_smul := by
        intro a b t
        change act W (a + b) t = act W a t + act W b t
        apply heq W
        intro U hUW
        apply (j U).injective
        simp only [hn, hact, map_add, add_smul]
      zero_smul := by
        intro t
        change act W 0 t = 0
        apply heq W
        intro U hUW
        apply (j U).injective
        simp only [hn, hact, map_zero, zero_smul] }
  let M := PresheafOfModules.ofPresheaf A.obj (fun {U V} f a t => hn f a t)
  let E : SheafOfModules.{u} R := ⟨M, by simpa only [M,
    PresheafOfModules.ofPresheaf_presheaf] using A.property⟩
  let ι (U : B) : E.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U :=
    { (j U) with
      map_smul' := fun a t => hact U a t }
  exact ⟨E, ι, hj⟩


/-- Finite gluing on a basis gives a module sheaf with compatible linear identifications.
Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009Q and 009T.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-basis).

Proof:
1. Regard the additive restriction maps as a functor of abelian groups on the basis.
   Every basis covering has a finite basis refinement by `hrefine`. Finite unique gluing,
   including the empty covering, therefore implies unique gluing on every basis covering
   by `lem-weil-pbc-basis-sheaf-cofinal-coverings` (009L).
2. Apply `lem-weil-pbc-sheaf-on-basis-extends` (009N/009Q) to this additive functor.
   It gives an abelian sheaf with additive equivalences on basis opens commuting with
   restrictions.
3. On a basis open, transport the scalar action through its additive equivalence.
   Semilinearity of the original restrictions says these actions are compatible.
   Apply `lem-weil-pbc-sheaf-morphism-on-basis` to extend the resulting maps of sets
   from the product of the ring presheaf and the abelian sheaf into the abelian sheaf.
   Naturality makes all restrictions semilinear. Each module axiom is equality of two
   natural maps into a sheaf. They agree on every basis open by the module axioms of F,
   hence agree everywhere by uniqueness of morphism extension (009T).
   The additive sheaf with these module structures is a sheaf of modules. The original
   additive equivalences are linear by the transported action and remain compatible
   with restrictions. This proves existence only; morphisms and stalks are separate. -/
private theorem exists_sheafOfModules_basis_extension
    (X : TopCat.{u}) (B : Set (Opens X)) (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (hrefine : ∀ (U : B) (C : Set B),
      (∀ V ∈ C, V.val ≤ U.val) → (⨆ V ∈ C, V.val) = U.val →
      ∃ (n : ℕ) (W : Fin n → B), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val)
    (R : TopCat.Sheaf RingCat.{u} X)
    (F : ∀ U : B, ModuleCat.{u} (R.obj.obj (op U.val)))
    (r : ∀ (U V : B), V.val ≤ U.val → F U →+ F V)
    (rid : ∀ (U : B) (s : F U), r U U le_rfl s = s)
    (rcomp : ∀ (U V W : B) (hVU : V.val ≤ U.val) (hWV : W.val ≤ V.val) (s : F U),
      r V W hWV (r U V hVU s) = r U W (hWV.trans hVU) s)
    (rsmul : ∀ (U V : B) (h : V.val ≤ U.val) (a : R.obj.obj (op U.val)) (s : F U),
      r U V h (a • s) = R.obj.map (homOfLE h).op a • r U V h s)
    (hglue : ∀ (U : B) (n : ℕ) (V : Fin n → B) (hV : ∀ i, (V i).val ≤ U.val),
      (⨆ i, (V i).val) = U.val → ∀ s : ∀ i, F (V i),
      (∀ i j,
        r (V i) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_left (s i) =
        r (V j) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_right (s j)) →
      ∃! t : F U, ∀ i, r U (V i) (hV i) t = s i) :
    ∃ (E : SheafOfModules.{u} R)
      (ι : ∀ U : B, E.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U),
      (∀ (U V : B) (h : V.val ≤ U.val) (t : E.val.obj (op U.val)),
        ι V (E.val.map (homOfLE h).op t) = r U V h (ι U t)) := by
  classical
  let Fab : Bᵒᵖ ⥤ AddCommGrpCat.{u} :=
    { obj := fun U => AddCommGrpCat.of (F U.unop)
      map := fun f => AddCommGrpCat.ofHom (r _ _ f.unop.le)
      map_id := by
        intro U
        ext s
        exact rid U.unop s
      map_comp := by
        intro U V W f g
        ext s
        exact (rcomp U.unop V.unop W.unop f.unop.le g.unop.le s).symm }
  let C : ∀ U : B, ∀ I : Type u, (I → {V : B // V ≤ U}) → Prop :=
    fun _ I _ => ∃ n : ℕ, Nonempty (I ≃ Fin n)
  have hall := gluing_of_cofinal_coverings B hB hcap (Fab ⋙ forget AddCommGrpCat) C
  have hcofinal : ∀ (U : B) (I : Type u) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∃ (J : Type u) (W : J → {Z : B // Z ≤ U}),
        (⨆ j, (W j).val.val) = U.val ∧ C U J W ∧
        ∃ α : J → I, ∀ j, (W j).val ≤ (V (α j)).val := by
    intro U I V hV
    let D : Set B := Set.range (fun i => (V i).val)
    have hD : (⨆ Z ∈ D, Z.val) = U.val := by
      simpa only [D, iSup_range] using hV
    obtain ⟨n, W, hW, hWV⟩ := hrefine U D
      (by rintro Z ⟨i, rfl⟩; exact (V i).property) hD
    have hWU (i : Fin n) : (W i).val ≤ U.val := by
      rw [← hW]
      exact le_iSup (fun j => (W j).val) i
    choose Z hZ hWZ using hWV
    choose α hα using hZ
    let W' : ULift.{u} (Fin n) → {Z : B // Z ≤ U} :=
      fun i => ⟨W i.down, hWU i.down⟩
    refine ⟨ULift.{u} (Fin n), W', ?_, ⟨n, ⟨Equiv.ulift⟩⟩, ?_⟩
    · change (⨆ i : ULift.{u} (Fin n), (W i.down).val) = U.val
      rw [← Equiv.ulift.symm.iSup_comp]
      exact hW
    · refine ⟨fun i => α i.down, ?_⟩
      intro i
      change (W i.down).val ≤ (V (α i.down)).val.val
      exact (hWZ i.down).trans_eq (congrArg Subtype.val (hα i.down)).symm
  have hselected : ∀ (U : B) (I : Type u) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val → C U I V →
      ∀ s : ∀ i, (Fab ⋙ forget AddCommGrpCat).obj (op (V i).val),
        (∀ i j,
          (Fab ⋙ forget AddCommGrpCat).map
            (homOfLE (show (⟨(V i).val.val ⊓ (V j).val.val,
              hcap (V i).val (V j).val⟩ : B) ≤ (V i).val from
                inf_le_left (a := (V i).val.val) (b := (V j).val.val))).op (s i) =
          (Fab ⋙ forget AddCommGrpCat).map
            (homOfLE (show (⟨(V i).val.val ⊓ (V j).val.val,
              hcap (V i).val (V j).val⟩ : B) ≤ (V j).val from
                inf_le_right (a := (V i).val.val) (b := (V j).val.val))).op (s j)) →
        ∃! t : (Fab ⋙ forget AddCommGrpCat).obj (op U),
          ∀ i, (Fab ⋙ forget AddCommGrpCat).map (homOfLE (V i).property).op t = s i := by
    intro U I V hV hC s hs
    obtain ⟨n, ⟨e⟩⟩ := hC
    obtain ⟨t, ht, huniq⟩ := hglue U n (fun i => (V (e.symm i)).val)
      (fun i => (V (e.symm i)).property) (by
        exact (e.symm.iSup_comp (g := fun i => (V i).val.val)).trans hV) (fun i => s (e.symm i))
      (fun i j => hs (e.symm i) (e.symm j))
    refine ⟨t, ?_, ?_⟩
    · intro i
      obtain ⟨k, rfl⟩ := e.symm.surjective i
      exact ht k
    · intro t' ht'
      exact huniq t' (fun i => ht' (e.symm i))
  obtain ⟨A, j, hj⟩ := exists_sheaf_extension_of_basis_gluing X B hB hcap Fab
    (hall hcofinal hselected)
  apply exists_module_structure_on_basis_extension X B hB R F r rsmul A
    (fun U => (j U).addCommGroupIsoToAddEquiv)
  exact hj


private theorem basisModule_hom_ext
    {X : TopCat.{u}} {B : Set (Opens X)} (hB : IsBasis B)
    {R : TopCat.Sheaf RingCat.{u} X} {E G : SheafOfModules.{u} R}
    {f g : E ⟶ G}
    (h : ∀ (U : B) (t : E.val.obj (op U.val)),
      f.val.app (op U.val) t = g.val.app (op U.val) t) : f = g := by
  apply (SheafOfModules.toSheaf R).map_injective
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext (B := fun U : B => U.val) E.val.presheaf
    ((SheafOfModules.toSheaf R).obj G)
    (by simpa only [Subtype.range_coe] using hB)
  intro U
  ext t
  exact h U t

private theorem basisModule_extend_hom
    {X : TopCat.{u}} {B : Set (Opens X)} (hB : IsBasis B)
    {R : TopCat.Sheaf RingCat.{u} X} (E G : SheafOfModules.{u} R)
    (α : ∀ U : B, E.val.obj (op U.val) →ₗ[R.obj.obj (op U.val)]
      G.val.obj (op U.val))
    (hα : ∀ (U V : B) (h : V.val ≤ U.val) (t : E.val.obj (op U.val)),
      α V (E.val.map (homOfLE h).op t) = G.val.map (homOfLE h).op (α U t)) :
    ∃! f : E ⟶ G, ∀ (U : B) (t : E.val.obj (op U.val)),
      f.val.app (op U.val) t = α U t := by
  classical
  let β : (inducedFunctor (fun U : B => U.val)).op ⋙ E.val.presheaf ⟶
      (inducedFunctor (fun U : B => U.val)).op ⋙ G.val.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (α U.unop).toAddMonoidHom
      naturality := by
        intro U V f
        ext t
        exact hα U.unop V.unop f.unop.hom.le t }
  have hb : IsBasis (Set.range (fun U : B => U.val)) := by
    simpa only [Subtype.range_coe] using hB
  let γ : E.val.presheaf ⟶ G.val.presheaf := TopCat.Sheaf.restrictHomEquivHom E.val.presheaf
    ((SheafOfModules.toSheaf R).obj G) hb β
  have hγ (U : B) (t : E.val.obj (op U.val)) : γ.app (op U.val) t = α U t := by
    change (TopCat.Sheaf.restrictHomEquivHom E.val.presheaf
      ((SheafOfModules.toSheaf R).obj G) hb β).app (op U.val) t = _
    rw [TopCat.Sheaf.extend_hom_app]
    rfl
  have hlin (W : (Opens X)ᵒᵖ) (a : R.obj.obj W) (t : E.val.obj W) :
      γ.app W (a • t) = a • (γ.app W t : G.val.obj W) := by
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf R).obj G) W.unop
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := hB.exists_subset_of_mem_open hx W.unop.isOpen
    change TopCat.Presheaf.germ G.val.presheaf W.unop x hx (γ.app W (a • t)) =
      TopCat.Presheaf.germ G.val.presheaf W.unop x hx (a • γ.app W t)
    rw [← TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hUW) x hxU,
      ← TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hUW) x hxU]
    congr 1
    have hn (s : E.val.obj W) :
        G.val.map (homOfLE hUW).op (γ.app W s) =
          γ.app (op U) (E.val.map (homOfLE hUW).op s) :=
      (CategoryTheory.congr_fun (γ.naturality (homOfLE hUW).op) s).symm
    change G.val.map (homOfLE hUW).op (γ.app W (a • t)) =
      G.val.map (homOfLE hUW).op (a • γ.app W t)
    rw [hn, E.val.map_smul, G.val.map_smul, hn, hγ ⟨U, hU⟩, hγ ⟨U, hU⟩, map_smul]
  let f : E ⟶ G := ⟨PresheafOfModules.homMk γ hlin⟩
  refine ⟨f, hγ, ?_⟩
  intro g hg
  exact basisModule_hom_ext hB (fun U t => (hg U t).trans (hγ U t).symm)

private theorem basisModule_isIso
    {X : TopCat.{u}} {B : Set (Opens X)} (hB : IsBasis B)
    {R : TopCat.Sheaf RingCat.{u} X} {E G : SheafOfModules.{u} R}
    (f : E ⟶ G) (hf : ∀ U : B, Function.Bijective (f.val.app (op U.val))) :
    IsIso f := by
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : B => U.val)
      (by simpa only [Subtype.range_coe] using hB)
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact hf U
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

private theorem basisModule_stalk_lift
    {X : TopCat.{u}} {B : Set (Opens X)} (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    {R : TopCat.Sheaf RingCat.{u} X} (E : SheafOfModules.{u} R)
    (x : X) (A : AddCommGrpCat.{u})
    (κ : ∀ U : {U : B // x ∈ U.val}, E.val.obj (op U.val.val) →+ A)
    (hκ : ∀ (U V : {U : B // x ∈ U.val}) (h : V.val.val ≤ U.val.val)
      (s : E.val.obj (op U.val.val)),
      κ V (E.val.map (homOfLE h).op s) = κ U s) :
    ∃! f : PresheafOfModules.stalkObj R.obj x E.val →+ A,
      ∀ (U : {U : B // x ∈ U.val}) (s : E.val.obj (op U.val.val)),
        f ((TopCat.Presheaf.germ E.val.presheaf U.val.val x U.property).hom s) = κ U s := by
  classical
  let S := Σ U : {U : B // x ∈ U.val}, E.val.obj (op U.val.val)
  let q : S → PresheafOfModules.stalkObj R.obj x E.val := fun s =>
    TopCat.Presheaf.germ E.val.presheaf s.1.val.val x s.1.property s.2
  let k : S → A := fun s => κ s.1 s.2
  have hk : k.FactorsThrough q := by
    rintro ⟨U, s⟩ ⟨V, t⟩ h
    obtain ⟨W, hxW, hW, hWU, hWV, heq⟩ :=
      TopCat.Presheaf.germ_eq_of_isBasis hB E.val.presheaf x U.property V.property h
    change κ U s = κ V t
    rw [← hκ U ⟨⟨W, hW⟩, hxW⟩ hWU, ← hκ V ⟨⟨W, hW⟩, hxW⟩ hWV]
    exact congrArg (κ ⟨⟨W, hW⟩, hxW⟩) heq
  let f₀ := Function.extend q k (fun _ => 0)
  have hq (U : {U : B // x ∈ U.val}) (s : E.val.obj (op U.val.val)) :
      f₀ (TopCat.Presheaf.germ E.val.presheaf U.val.val x U.property s) = κ U s :=
    hk.extend_apply (fun _ => 0) ⟨U, s⟩
  have hsurj : Function.Surjective q := by
    intro m
    obtain ⟨U, hxU, hU, s, hs⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB E.val.presheaf x m
    exact ⟨⟨⟨⟨U, hU⟩, hxU⟩, s⟩, hs⟩
  have hadd (m n : PresheafOfModules.stalkObj R.obj x E.val) :
      f₀ (m + n) = f₀ m + f₀ n := by
    obtain ⟨⟨U, s⟩, rfl⟩ := hsurj m
    obtain ⟨⟨V, t⟩, rfl⟩ := hsurj n
    let W : {U : B // x ∈ U.val} :=
      ⟨⟨U.val.val ⊓ V.val.val, hcap U.val V.val⟩, ⟨U.property, V.property⟩⟩
    change f₀ (TopCat.Presheaf.germ E.val.presheaf U.val.val x U.property s +
      TopCat.Presheaf.germ E.val.presheaf V.val.val x V.property t) =
      f₀ (TopCat.Presheaf.germ E.val.presheaf U.val.val x U.property s) +
        f₀ (TopCat.Presheaf.germ E.val.presheaf V.val.val x V.property t)
    rw [← TopCat.Presheaf.germ_res_apply E.val.presheaf
        (homOfLE inf_le_left : W.val.val ⟶ U.val.val) x W.property s,
      ← TopCat.Presheaf.germ_res_apply E.val.presheaf
        (homOfLE inf_le_right : W.val.val ⟶ V.val.val) x W.property t]
    rw [← map_add, hq W, hq W, hq W, map_add]
  let f : PresheafOfModules.stalkObj R.obj x E.val →+ A :=
    { toFun := f₀
      map_zero' := by
        have h := hadd 0 0
        simpa using h
      map_add' := hadd }
  refine ⟨f, hq, ?_⟩
  intro g hg
  ext m
  obtain ⟨⟨U, s⟩, rfl⟩ := hsurj m
  exact (hg U s).trans (hq U s).symm

/-- A module presheaf on an intersection-closed basis with finite refinements and finite
unique gluing extends to a sheaf of modules, with its universal property and basis stalks.
Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-basis).

Proof:
1. Finite basis coverings form a cofinal system of coverings by the finite-refinement
   hypothesis. Apply `lem-weil-pbc-basis-sheaf-cofinal-coverings` (009L) to obtain gluing
   for all basis coverings, including the empty covering.
2. Apply `lem-weil-pbc-sheaf-on-basis-extends` (009N and 009Q) to the underlying abelian
   presheaf to obtain the abelian sheaf and restriction-compatible additive identifications.
3. Transport scalar multiplication on basis opens along those identifications. Extend the
   resulting map from the product of the ring presheaf and the abelian sheaf into the sheaf
   using `lem-weil-pbc-sheaf-morphism-on-basis`. Each module axiom is an equality of maps
   into a sheaf, true on the basis, hence everywhere by the same lemma. Naturality gives
   semilinearity of restrictions, and the identifications are linear (009T).
4. Extend each compatible family of linear maps by the morphism-extension lemma. Compare
   the two scalar-action maps on the basis to obtain linearity globally. Uniqueness follows
   from uniqueness for abelian sheaves. Basiswise bijectivity implies an isomorphism; its
   inverse is linear. Apply this to the inverse identifications of another extension to
   obtain uniqueness up to unique isomorphism (009U).
5. By `lem-weil-pbc-stalk-germs-on-basis`, every stalk element has a basis representative,
   and equal representatives agree after a basis restriction. Thus compatible additive
   maps on basis neighbourhoods descend uniquely to the stalk. Addition is checked on a
   common basis neighbourhood. The germ scalar formula from `def-weil-pbc-module-stalk`
   identifies the module action with the action on this colimit. -/
theorem exists_sheafOfModules_from_basis
    (X : TopCat.{u}) (B : Set (Opens X)) (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (hrefine : ∀ (U : B) (C : Set B),
      (∀ V ∈ C, V.val ≤ U.val) → (⨆ V ∈ C, V.val) = U.val →
      ∃ (n : ℕ) (W : Fin n → B), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val)
    (R : TopCat.Sheaf RingCat.{u} X)
    (F : ∀ U : B, ModuleCat.{u} (R.obj.obj (op U.val)))
    (r : ∀ (U V : B), V.val ≤ U.val → F U →+ F V)
    (rid : ∀ (U : B) (s : F U), r U U le_rfl s = s)
    (rcomp : ∀ (U V W : B) (hVU : V.val ≤ U.val) (hWV : W.val ≤ V.val) (s : F U),
      r V W hWV (r U V hVU s) = r U W (hWV.trans hVU) s)
    (rsmul : ∀ (U V : B) (h : V.val ≤ U.val) (a : R.obj.obj (op U.val)) (s : F U),
      r U V h (a • s) = R.obj.map (homOfLE h).op a • r U V h s)
    (hglue : ∀ (U : B) (n : ℕ) (V : Fin n → B) (hV : ∀ i, (V i).val ≤ U.val),
      (⨆ i, (V i).val) = U.val → ∀ s : ∀ i, F (V i),
      (∀ i j,
        r (V i) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_left (s i) =
        r (V j) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_right (s j)) →
      ∃! t : F U, ∀ i, r U (V i) (hV i) t = s i) :
    ∃ (E : SheafOfModules.{u} R)
      (ι : ∀ U : B, E.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U),
      (∀ (U V : B) (h : V.val ≤ U.val) (t : E.val.obj (op U.val)),
        ι V (E.val.map (homOfLE h).op t) = r U V h (ι U t)) ∧
      (∀ (G : SheafOfModules.{u} R)
        (ψ : ∀ U : B, F U →ₗ[R.obj.obj (op U.val)] G.val.obj (op U.val)),
        (∀ (U V : B) (h : V.val ≤ U.val) (s : F U),
          ψ V (r U V h s) = G.val.map (homOfLE h).op (ψ U s)) →
        (∃! Ψ : E ⟶ G, ∀ (U : B) (t : E.val.obj (op U.val)),
          Ψ.val.app (op U.val) t = ψ U (ι U t)) ∧
        (∀ (Ψ : E ⟶ G),
          (∀ (U : B) (t : E.val.obj (op U.val)),
            Ψ.val.app (op U.val) t = ψ U (ι U t)) →
          (∀ U : B, Function.Bijective (ψ U)) → IsIso Ψ)) ∧
      (∀ (G : SheafOfModules.{u} R)
        (j : ∀ U : B, G.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U),
        (∀ (U V : B) (h : V.val ≤ U.val) (t : G.val.obj (op U.val)),
          j V (G.val.map (homOfLE h).op t) = r U V h (j U t)) →
        ∃! e : E ≅ G, ∀ (U : B) (t : E.val.obj (op U.val)),
          j U (e.hom.val.app (op U.val) t) = ι U t) ∧
      (∀ (x : X) (A : AddCommGrpCat.{u})
        (φ : ∀ U : {U : B // x ∈ U.val}, F U.val →+ A),
        (∀ (U V : {U : B // x ∈ U.val}) (h : V.val.val ≤ U.val.val) (s : F U.val),
          φ V (r U.val V.val h s) = φ U s) →
        ∃! f : PresheafOfModules.stalkObj R.obj x E.val →+ A,
          ∀ (U : {U : B // x ∈ U.val}) (s : F U.val),
            f ((TopCat.Presheaf.germ (X := X) E.val.presheaf U.val.val x U.property).hom
              ((ι U.val).symm s)) = φ U s) ∧
      (∀ (x : X) (U : B) (hx : x ∈ U.val) (a : R.obj.obj (op U.val)) (s : F U),
        (TopCat.Presheaf.germ (X := X) E.val.presheaf U.val x hx).hom
          ((ι U).symm (a • s)) =
          TopCat.Presheaf.germ (X := X) R.obj U.val x hx a •
            (TopCat.Presheaf.germ (X := X) E.val.presheaf U.val x hx).hom ((ι U).symm s)) := by
  classical
  obtain ⟨E, ι, hι⟩ := exists_sheafOfModules_basis_extension
    X B hB hcap hrefine R F r rid rcomp rsmul hglue
  have hext (G : SheafOfModules.{u} R)
      (ψ : ∀ U : B, F U →ₗ[R.obj.obj (op U.val)] G.val.obj (op U.val))
      (hψ : ∀ (U V : B) (h : V.val ≤ U.val) (s : F U),
        ψ V (r U V h s) = G.val.map (homOfLE h).op (ψ U s)) :
      ∃! Ψ : E ⟶ G, ∀ (U : B) (t : E.val.obj (op U.val)),
        Ψ.val.app (op U.val) t = ψ U (ι U t) := by
    apply basisModule_extend_hom hB E G (fun U => (ψ U).comp (ι U).toLinearMap)
    intro U V h t
    change ψ V (ι V (E.val.map (homOfLE h).op t)) = _
    rw [hι, hψ]
    rfl
  refine ⟨E, ι, hι, ?_, ?_, ?_, ?_⟩
  · intro G ψ hψ
    refine ⟨hext G ψ hψ, ?_⟩
    intro Ψ hΨ hbij
    apply basisModule_isIso hB Ψ
    intro U
    have hh : (fun t => Ψ.val.app (op U.val) t) = fun t => ψ U (ι U t) :=
      funext (hΨ U)
    convert (hbij U).comp (ι U).bijective using 1
    exact hh
  · intro G j hj
    let ψ := fun U : B => (j U).symm.toLinearMap
    have hψ : ∀ (U V : B) (h : V.val ≤ U.val) (s : F U),
        ψ V (r U V h s) = G.val.map (homOfLE h).op (ψ U s) := by
      intro U V h s
      apply (j V).injective
      dsimp [ψ]
      rw [LinearEquiv.apply_symm_apply, hj, LinearEquiv.apply_symm_apply]
    obtain ⟨f, hf, huniq⟩ := hext G ψ hψ
    have : IsIso f := basisModule_isIso hB f (fun U => by
      have hh : (fun t => f.val.app (op U.val) t) = fun t => ψ U (ι U t) :=
        funext (hf U)
      convert (j U).symm.bijective.comp (ι U).bijective using 1
      exact hh)
    refine ⟨asIso f, ?_, ?_⟩
    · intro U t
      change j U (f.val.app (op U.val) t) = ι U t
      rw [hf]
      exact (j U).apply_symm_apply _
    · intro e he
      apply Iso.ext
      apply huniq e.hom
      intro U t
      apply (j U).injective
      exact (he U t).trans ((j U).apply_symm_apply _).symm
  · intro x A φ hφ
    let κ := fun U : {U : B // x ∈ U.val} =>
      (φ U).comp (ι U.val).toAddEquiv.toAddMonoidHom
    have hκ : ∀ (U V : {U : B // x ∈ U.val}) (h : V.val.val ≤ U.val.val)
        (s : E.val.obj (op U.val.val)),
        κ V (E.val.map (homOfLE h).op s) = κ U s := by
      intro U V h s
      change φ V (ι V.val (E.val.map (homOfLE h).op s)) = _
      rw [hι, hφ]
      rfl
    obtain ⟨f, hf, huniq⟩ := basisModule_stalk_lift hB hcap E x A κ hκ
    refine ⟨f, ?_, ?_⟩
    · intro U s
      rw [hf]
      change φ U (ι U.val ((ι U.val).symm s)) = φ U s
      rw [LinearEquiv.apply_symm_apply]
    · intro g hg
      apply huniq g
      intro U t
      change g ((TopCat.Presheaf.germ E.val.presheaf U.val.val x U.property).hom t) =
        φ U (ι U.val t)
      simpa only [LinearEquiv.symm_apply_apply] using hg U (ι U.val t)
  · intro x U hx a s
    rw [map_smul]
    exact E.val.germ_ringCat_smul x U.val hx a ((ι U).symm s)

end TopologicalSpace.Opens
