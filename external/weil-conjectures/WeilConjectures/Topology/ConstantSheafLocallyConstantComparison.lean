/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero

/-!
# The locally constant description of the constant abelian sheaf

Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081.
(blueprint: lem-sc-constant-sheaf-locally-constant-comparison)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat

private theorem abelian_underlying_isSheaf (X : TopCat.{u})
    (F : X.Sheaf AddCommGrpCat.{v}) :
    Presheaf.IsSheaf (F.obj ⋙ forget AddCommGrpCat.{v}) := by
  apply (CategoryTheory.Presheaf.isSheaf_of_iso_iff
    (Functor.isoWhiskerLeft F.obj AddCommGrpCat.coyonedaObjIsoForget)).1
  exact (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2
    (F.property (AddCommGrpCat.of (ULift.{v} ℤ)))

private theorem abelian_section_ext (X : TopCat.{u}) (F : X.Sheaf AddCommGrpCat.{v})
    (U : Opens X) (s t : F.obj.obj (op U))
    (hst : ∀ x : U, ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
      F.obj.map (homOfLE hVU).op s = F.obj.map (homOfLE hVU).op t) : s = t := by
  classical
  have hF := (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp
    (abelian_underlying_isSheaf X F)
  choose V hV hxV H using hst
  refine (hF.isSheafFor (.ofArrows V fun x ↦ homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · exact fun x hx ↦ ⟨V ⟨x, hx⟩, homOfLE (hV _),
      Sieve.ofArrows_mk _ _ _, hxV _⟩
  · rintro _ _ ⟨x⟩
    exact H x

private theorem abelian_gluing (X : TopCat.{u}) (F : X.Sheaf AddCommGrpCat.{v})
    {ι : Type*} (V : ι → Opens X) (U : Opens X) (hV : ∀ i, V i ≤ U)
    (hcover : U ≤ iSup V) (sf : ∀ i, F.obj.obj (op (V i)))
    (hc : Presheaf.IsCompatible F.obj V sf) :
    ∃ s : F.obj.obj (op U), ∀ i, F.obj.map (homOfLE (hV i)).op s = sf i := by
  classical
  have hU : U = iSup V := le_antisymm hcover (iSup_le hV)
  obtain ⟨s, hs, _⟩ := (abelian_underlying_isSheaf X F).isSheafUniqueGluing_types sf hc
  refine ⟨F.obj.map (eqToHom hU).op s, ?_⟩
  intro i
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  exact hs i

private theorem skyscraper_abelian_isSheaf (X : TopCat.{u}) (x : X)
    (A : AddCommGrpCat.{v}) [∀ U : Opens X, Decidable (x ∈ U)] :
    Presheaf.IsSheaf (skyscraperPresheaf x A) := by
  classical
  let Q := skyscraperPresheaf x A
  have hi (U : Opens X) (hx : x ∈ U) : Q.obj (op U) = A := ite_eq_left hx
  have ht (U : Opens X) (hx : x ∉ U) : Q.obj (op U) = Limits.terminal _ := ite_eq_right hx
  have hmap (U V : Opens X) (hVU : V ≤ U) (hx : x ∈ V) :
      Q.map (homOfLE hVU).op = eqToHom ((hi U (hVU hx)).trans (hi V hx).symm) := by
    dsimp [Q, skyscraperPresheaf]
    rw [dite_eq_left hx]
  have hsub (U : Opens X) (hx : x ∉ U) : Subsingleton (Q.obj (op U)) := by
    rw [ht U hx]
    exact (AddCommGrpCat.subsingleton_of_isZero
      ((Limits.isZero_zero AddCommGrpCat.{v}).of_iso
        Limits.HasZeroObject.zeroIsoTerminal.symm))
  apply CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp
    (Opens.grothendieckTopology X) Q (forget AddCommGrpCat.{v})
  apply (Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).2
  intro ι V sf hc
  by_cases hx : x ∈ iSup V
  · obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    let s : Q.obj (op (iSup V)) :=
      eqToHom ((hi (V i) hxi).trans (hi (iSup V) hx).symm) (sf i)
    have hs : Presheaf.IsGluing (Q ⋙ forget AddCommGrpCat.{v}) V sf s := by
      intro j
      by_cases hxj : x ∈ V j
      · have hij := hc i j
        change Q.map (homOfLE inf_le_left).op (sf i) =
          Q.map (homOfLE inf_le_right).op (sf j) at hij
        rw [hmap (V i) (V i ⊓ V j) inf_le_left ⟨hxi, hxj⟩,
          hmap (V j) (V i ⊓ V j) inf_le_right ⟨hxi, hxj⟩] at hij
        change Q.map (homOfLE (le_iSup V j)).op s = sf j
        rw [hmap (iSup V) (V j) (le_iSup V j) hxj]
        have hh := congrArg
          (fun z ↦ eqToHom ((hi (V i ⊓ V j) ⟨hxi, hxj⟩).trans (hi (V j) hxj).symm) z)
          hij
        simpa [s, ← ConcreteCategory.comp_apply] using hh
      · exact (hsub (V j) hxj).elim _ _
    refine ⟨s, hs, ?_⟩
    intro t ht
    have ht' := ht i
    change Q.map (homOfLE (le_iSup V i)).op t = sf i at ht'
    rw [hmap (iSup V) (V i) (le_iSup V i) hxi] at ht'
    have hh := congrArg
      (fun z ↦ eqToHom ((hi (V i) hxi).trans (hi (iSup V) hx).symm) z) ht'
    simpa [s, ← ConcreteCategory.comp_apply] using hh
  · refine ⟨0, ?_, ?_⟩
    · intro i
      have hxi : x ∉ V i := fun hi ↦ hx (Opens.mem_iSup.mpr ⟨i, hi⟩)
      exact (hsub (V i) hxi).elim _ _
    · intro t _
      exact (hsub (iSup V) hx).elim _ _

private theorem unit_inj (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : Type v) [AddCommGroup A] (U : Opens X) (x : U) :
    Function.Injective ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))).app (op U)) := by
  classical
  let P := (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A)
  let Q := skyscraperPresheaf x.1 (AddCommGrpCat.of A)
  have hQ := skyscraper_abelian_isSheaf X x.1 (AddCommGrpCat.of A)
  let c : P ⟶ Q :=
    { app := fun V ↦ if h : x.1 ∈ V.unop then eqToHom (ite_eq_left h).symm
        else Limits.terminal.from _ ≫ eqToHom (ite_eq_right h).symm
      naturality := by
        intro V W i
        by_cases hw : x.1 ∈ W.unop
        · have hv : x.1 ∈ V.unop := i.unop.le hw
          simp [P, Q, skyscraperPresheaf, hw, hv]
        · have ht : Limits.IsTerminal (Q.obj W) :=
            Limits.IsTerminal.ofIso Limits.terminalIsTerminal (eqToIso (ite_eq_right hw)).symm
          exact ht.hom_ext _ _ }
  let l := sheafifyLift (Opens.grothendieckTopology X) c hQ
  have hfac := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_sheafifyLift (Opens.grothendieckTopology X)
      c hQ) (op U))
  intro a b hab
  have heq := congrArg (fun s ↦ l.app (op U) s) hab
  have ha := hfac a
  have hb := hfac b
  change l.app (op U) (_) = c.app (op U) a at ha
  change l.app (op U) (_) = c.app (op U) b at hb
  have hc : c.app (op U) a = c.app (op U) b := ha.symm.trans (heq.trans hb)
  have hi : IsIso (c.app (op U)) := by
    dsimp [c]
    rw [dite_eq_left x.2]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso (c.app (op U))).injective hc

private theorem constantSheaf_unit_localSurj (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : Type v) [AddCommGroup A] :
    let F := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
      (AddCommGrpCat.of A)
    let η := toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))
    ∀ (U : Opens X) (s : F.obj.obj (op U)) (x : U),
      ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
        ∃ a : A, η.app (op V) a = F.obj.map (homOfLE hVU).op s := by
  classical
  let F := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of A)
  let η := toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))
  let hlocal (U : Opens X) (s : F.obj.obj (op U)) : Prop :=
    ∀ x : U, ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ a : A, η.app (op V) a = F.obj.map (homOfLE hVU).op s
  have hη (U V : Opens X) (hVU : V ≤ U) (a : A) :
      F.obj.map (homOfLE hVU).op (η.app (op U) a) = η.app (op V) a := by
    exact (ConcreteCategory.congr_hom (η.naturality (homOfLE hVU).op) a).symm
  have hcomp (U V W : Opens X) (hVU : V ≤ U) (hWV : W ≤ V)
      (s : F.obj.obj (op U)) :
      F.obj.map (homOfLE hWV).op (F.obj.map (homOfLE hVU).op s) =
        F.obj.map (homOfLE (hWV.trans hVU)).op s := by
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    rfl
  have hres (U V : Opens X) (hVU : V ≤ U) (s : F.obj.obj (op U)) (hs : hlocal U s) :
      hlocal V (F.obj.map (homOfLE hVU).op s) := by
    intro x
    obtain ⟨W, hWU, hxW, a, ha⟩ := hs ⟨x.1, hVU x.2⟩
    refine ⟨W ⊓ V, inf_le_right, ⟨hxW, x.2⟩, a, ?_⟩
    rw [hcomp, ← hη W (W ⊓ V) inf_le_left a, ha, hcomp]
  let K (U : Opens X) : AddSubgroup (F.obj.obj (op U)) :=
    { carrier := {s | hlocal U s}
      zero_mem' := by
        intro x
        exact ⟨U, le_rfl, x.2, 0, by simp⟩
      add_mem' := by
        intro s t hs ht x
        obtain ⟨V, hVU, hxV, a, ha⟩ := hs x
        obtain ⟨W, hWU, hxW, b, hb⟩ := ht x
        refine ⟨V ⊓ W, (inf_le_left : V ⊓ W ≤ V).trans hVU,
          ⟨hxV, hxW⟩, a + b, ?_⟩
        rw [map_add, map_add]
        congr 1
        · rw [← hη V (V ⊓ W) inf_le_left a, ha, hcomp]
        · rw [← hη W (V ⊓ W) inf_le_right b, hb, hcomp]
      neg_mem' := by
        intro s hs x
        obtain ⟨V, hVU, hxV, a, ha⟩ := hs x
        refine ⟨V, hVU, hxV, -a, ?_⟩
        rw [map_neg, map_neg, ha] }
  let Q : X.Presheaf AddCommGrpCat.{v} :=
    { obj := fun U ↦ AddCommGrpCat.of (K U.unop)
      map := fun {U V} i ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ⟨F.obj.map i s.1, hres U.unop V.unop i.unop.le s.1 s.2⟩
          map_zero' := by apply Subtype.ext; exact map_zero _
          map_add' := by intro s t; apply Subtype.ext; exact map_add _ _ _ }
      map_id := by intro U; ext s; exact ConcreteCategory.congr_hom (F.obj.map_id U) s.1
      map_comp := by
        intro U V W i j
        ext s
        exact ConcreteCategory.congr_hom (F.obj.map_comp i j) s.1 }
  have hQ : Presheaf.IsSheaf Q := by
    apply CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp
      (Opens.grothendieckTopology X) Q (forget AddCommGrpCat.{v})
    apply (Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).2
    intro ι V sf hc
    have hcF : Presheaf.IsCompatible F.obj V (fun i ↦ (sf i).1) := by
      intro i j
      exact congrArg Subtype.val (hc i j)
    obtain ⟨s, hs, huniq⟩ := (abelian_underlying_isSheaf X F).isSheafUniqueGluing_types
      (fun i ↦ (sf i).1) hcF
    have hls : hlocal (iSup V) s := by
      intro x
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp x.2
      obtain ⟨W, hWV, hxW, a, ha⟩ := (sf i).2 ⟨x.1, hxi⟩
      refine ⟨W, hWV.trans (le_iSup V i), hxW, a, ?_⟩
      have hsi : F.obj.map (homOfLE (le_iSup V i)).op s = (sf i).1 := hs i
      rw [← hcomp (iSup V) (V i) W (le_iSup V i) hWV s, hsi]
      exact ha
    refine ⟨⟨s, hls⟩, ?_, ?_⟩
    · intro i
      apply Subtype.ext
      exact hs i
    · intro t ht
      apply Subtype.ext
      apply huniq
      intro i
      exact congrArg Subtype.val (ht i)
  let c : (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A) ⟶ Q :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun a ↦ ⟨η.app U a, fun x ↦ ⟨U.unop, le_rfl, x.2, a, by simp⟩⟩
          map_zero' := by apply Subtype.ext; exact map_zero _
          map_add' := by intro a b; apply Subtype.ext; exact map_add _ _ _ }
      naturality := by
        intro U V i
        ext a
        exact ConcreteCategory.congr_hom (η.naturality i) a }
  let inc : Q ⟶ F.obj :=
    { app := fun U ↦ AddCommGrpCat.ofHom (K U.unop).subtype
      naturality := by intro U V i; rfl }
  let l := sheafifyLift (Opens.grothendieckTopology X) c hQ
  have hi : l ≫ inc = 𝟙 F.obj := by
    apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ F.property
    rw [← Category.assoc, toSheafify_sheafifyLift]
    rfl
  change ∀ (U : Opens X) (s : F.obj.obj (op U)) (x : U),
    ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ a : A, η.app (op V) a = F.obj.map (homOfLE hVU).op s
  intro U s x
  have heq := ConcreteCategory.congr_hom (NatTrans.congr_app hi (op U)) s
  change (l.app (op U) s).1 = s at heq
  rw [← heq]
  exact (l.app (op U) s).2 x


/-- The constant abelian sheaf is naturally the group of locally constant maps on opens.

Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081.
(blueprint: lem-sc-constant-sheaf-locally-constant-comparison)
Proof: first extract elementwise gluing and separation from the abelian sheaf condition
using the corepresentability of the forgetful functor by the lifted integers. The
subgroups of sections locally in the image of the constant-presheaf unit form a sheaf:
local representatives are stable under restriction, addition on common intersections,
and negation; gluing preserves the local representative property. The unit factors
through this subsheaf. Its sheafification lift followed by the inclusion is the identity,
by uniqueness of sheafification, so every section is locally represented by a constant.
For a point x, the presheaf with value A on opens containing x and the trivial group
elsewhere is a sheaf, directly by gluing. Factoring the constant presheaf map to this
skyscraper sheaf through sheafification proves the unit injective on every open containing
x. This proof does not require the space and coefficient universes to coincide.
Assign to a section at x the value of any local constant representative. On intersections
the injectivity just proved makes this value independent of the representative. The
resulting function is locally constant. Restriction and addition follow by comparing
representatives on a common neighbourhood. Equality of these functions implies local,
hence global, equality of sections. Conversely, the constant sections on the open fibres
of a locally constant function agree on overlaps and glue to a section with that function.
The resulting bijective additive maps are the required additive equivalences; restriction
compatibility was proved pointwise. Empty opens are included: separation is vacuous and
the gluing argument works with all fibres empty. -/
theorem constantSheaf_locallyConstant_comparison
    (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : Type v) [AddCommGroup A] :
    ∃ e : ∀ U : Opens X,
      AddEquiv (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of A)).1.obj (op U)) (LocallyConstant U A),
      ∀ (U V : Opens X) (hVU : V ≤ U) (s :
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.obj (op U)) (x : V),
        e V (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.map (homOfLE hVU).op s) x =
            e U s ⟨x.1, hVU x.2⟩ := by
  classical
  let F := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of A)
  let η := toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of A))
  have hloc := constantSheaf_unit_localSurj X A
  have hinj := unit_inj X A
  change (∀ (U : Opens X) (s : F.obj.obj (op U)) (x : U),
    ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ a : A, η.app (op V) a = F.obj.map (homOfLE hVU).op s) at hloc
  change (∀ (U : Opens X) (_x : U), Function.Injective (η.app (op U))) at hinj
  have hη (U V : Opens X) (hVU : V ≤ U) (a : A) :
      F.obj.map (homOfLE hVU).op (η.app (op U) a) = η.app (op V) a := by
    exact (ConcreteCategory.congr_hom (η.naturality (homOfLE hVU).op) a).symm
  have hcomp (U V W : Opens X) (hVU : V ≤ U) (hWV : W ≤ V)
      (s : F.obj.obj (op U)) :
      F.obj.map (homOfLE hWV).op (F.obj.map (homOfLE hVU).op s) =
        F.obj.map (homOfLE (hWV.trans hVU)).op s := by
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    rfl
  have hex (U : Opens X) (s : F.obj.obj (op U)) (x : U) :
      ∃ a : A, ∃ (V : Opens X) (hVU : V ≤ U), x.1 ∈ V ∧
        η.app (op V) a = F.obj.map (homOfLE hVU).op s := by
    obtain ⟨V, hVU, hxV, a, ha⟩ := hloc U s x
    exact ⟨a, V, hVU, hxV, ha⟩
  let val (U : Opens X) (s : F.obj.obj (op U)) (x : U) := (hex U s x).choose
  have hval (U : Opens X) (s : F.obj.obj (op U)) (x : U) := (hex U s x).choose_spec
  have hvalue (U V : Opens X) (hVU : V ≤ U) (s : F.obj.obj (op U))
      (x : V) (a : A) (ha : η.app (op V) a = F.obj.map (homOfLE hVU).op s) :
      val U s ⟨x.1, hVU x.2⟩ = a := by
    obtain ⟨W, hWU, hxW, hw⟩ := hval U s ⟨x.1, hVU x.2⟩
    apply hinj (W ⊓ V) ⟨x.1, hxW, x.2⟩
    calc
      η.app (op (W ⊓ V)) (val U s ⟨x.1, hVU x.2⟩) =
          F.obj.map (homOfLE inf_le_left).op (η.app (op W) _) :=
        (hη W (W ⊓ V) inf_le_left _).symm
      _ = F.obj.map (homOfLE ((inf_le_left : W ⊓ V ≤ W).trans hWU)).op s := by
        rw [hw, hcomp]
      _ = F.obj.map (homOfLE ((inf_le_right : W ⊓ V ≤ V).trans hVU)).op s := rfl
      _ = F.obj.map (homOfLE inf_le_right).op (η.app (op V) a) := by
        rw [ha, hcomp]
      _ = η.app (op (W ⊓ V)) a := hη V (W ⊓ V) inf_le_right a
  have hconst (U : Opens X) (a : A) (x : U) : val U (η.app (op U) a) x = a := by
    exact hvalue U U le_rfl _ x a (by simp)
  have hlocal (U : Opens X) (s : F.obj.obj (op U)) : IsLocallyConstant (val U s) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro x
    obtain ⟨V, hVU, hxV, ha⟩ := hval U s x
    refine ⟨{y : U | y.1 ∈ V}, V.isOpen.preimage continuous_subtype_val, hxV, ?_⟩
    intro y hy
    exact hvalue U V hVU s ⟨y.1, hy⟩ (val U s x) ha
  let ev (U : Opens X) (s : F.obj.obj (op U)) : LocallyConstant U A :=
    ⟨val U s, hlocal U s⟩
  have hev_res (U V : Opens X) (hVU : V ≤ U) (s : F.obj.obj (op U)) (x : V) :
      ev V (F.obj.map (homOfLE hVU).op s) x = ev U s ⟨x.1, hVU x.2⟩ := by
    obtain ⟨W, hWV, hxW, a, ha⟩ := hloc V (F.obj.map (homOfLE hVU).op s) x
    have ha' : η.app (op W) a = F.obj.map (homOfLE (hWV.trans hVU)).op s := by
      rw [ha, hcomp]
    exact (hvalue V W hWV _ ⟨x.1, hxW⟩ a ha).trans
      (hvalue U W (hWV.trans hVU) s ⟨x.1, hxW⟩ a ha').symm
  have hev_add (U : Opens X) (s t : F.obj.obj (op U)) :
      ev U (s + t) = ev U s + ev U t := by
    ext x
    obtain ⟨V, hVU, hxV, a, ha⟩ := hloc U s x
    obtain ⟨W, hWU, hxW, b, hb⟩ := hloc U t x
    have hab : η.app (op (V ⊓ W)) (a + b) =
        F.obj.map (homOfLE ((inf_le_left : V ⊓ W ≤ V).trans hVU)).op (s + t) := by
      rw [map_add, map_add]
      congr 1
      · rw [← hη V (V ⊓ W) inf_le_left a, ha, hcomp]
      · rw [← hη W (V ⊓ W) inf_le_right b, hb, hcomp]
    exact (hvalue U (V ⊓ W) ((inf_le_left : V ⊓ W ≤ V).trans hVU) (s + t)
      ⟨x.1, hxV, hxW⟩ (a + b) hab).trans
        (congrArg₂ (· + ·) (hvalue U V hVU s ⟨x.1, hxV⟩ a ha)
          (hvalue U W hWU t ⟨x.1, hxW⟩ b hb)).symm
  have hev_zero (U : Opens X) : ev U 0 = 0 := by
    ext x
    change val U 0 x = 0
    have hc := hconst U 0 x
    simpa using hc
  let e (U : Opens X) : F.obj.obj (op U) →+ LocallyConstant U A :=
    { toFun := ev U
      map_zero' := hev_zero U
      map_add' := hev_add U }
  have hev_inj (U : Opens X) : Function.Injective (e U) := by
    intro s t hst
    apply abelian_section_ext X F U s t
    intro x
    obtain ⟨V, hVU, hxV, a, ha⟩ := hloc U s x
    obtain ⟨W, hWU, hxW, b, hb⟩ := hloc U t x
    have hab : a = b := by
      have hh := congrArg (fun f : LocallyConstant U A ↦ f x) hst
      change val U s x = val U t x at hh
      rw [hvalue U V hVU s ⟨x.1, hxV⟩ a ha,
        hvalue U W hWU t ⟨x.1, hxW⟩ b hb] at hh
      exact hh
    refine ⟨V ⊓ W, (inf_le_left : V ⊓ W ≤ V).trans hVU, ⟨hxV, hxW⟩, ?_⟩
    calc
      F.obj.map (homOfLE ((inf_le_left : V ⊓ W ≤ V).trans hVU)).op s =
          η.app (op (V ⊓ W)) a := by
        rw [← hcomp U V (V ⊓ W) hVU inf_le_left s, ← ha, hη]
      _ = η.app (op (V ⊓ W)) b := congrArg _ hab
      _ = F.obj.map (homOfLE ((inf_le_left : V ⊓ W ≤ V).trans hVU)).op t := by
        rw [← hη W (V ⊓ W) inf_le_right b, hb, hcomp]
  have hev_surj (U : Opens X) : Function.Surjective (e U) := by
    intro f
    let V (a : A) : Opens X :=
      ⟨Subtype.val '' {x : U | f x = a},
        U.isOpen.isOpenMap_subtype_val _ (f.isLocallyConstant.isOpen_fiber a)⟩
    have hVU (a : A) : V a ≤ U := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    have hVa (a : A) (x : V a) : f ⟨x.1, hVU a x.2⟩ = a := by
      obtain ⟨y, hy, hxy⟩ := x.2
      have heq : (⟨x.1, hVU a x.2⟩ : U) = y := Subtype.ext hxy.symm
      rw [heq]
      exact hy
    have hcover : U ≤ iSup V := by
      intro x hx
      exact Opens.mem_iSup.mpr ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
    have hc : Presheaf.IsCompatible F.obj V (fun a ↦ η.app (op (V a)) a) := by
      intro a b
      apply abelian_section_ext X F (V a ⊓ V b)
      intro x
      have hab : a = b :=
        (hVa a ⟨x.1, x.2.1⟩).symm.trans (hVa b ⟨x.1, x.2.2⟩)
      refine ⟨V a ⊓ V b, le_rfl, x.2, ?_⟩
      change F.obj.map (𝟙 (op (V a ⊓ V b))) _ =
        F.obj.map (𝟙 (op (V a ⊓ V b))) _
      rw [F.obj.map_id]
      change F.obj.map (homOfLE inf_le_left).op (η.app (op (V a)) a) =
        F.obj.map (homOfLE inf_le_right).op (η.app (op (V b)) b)
      rw [hη, hη, hab]
    obtain ⟨s, hs⟩ := abelian_gluing X F V U hVU hcover
      (fun a ↦ η.app (op (V a)) a) hc
    refine ⟨s, ?_⟩
    apply LocallyConstant.ext
    intro x
    let y : V (f x) := ⟨x.1, ⟨x, rfl, rfl⟩⟩
    exact hvalue U (V (f x)) (hVU (f x)) s y (f x) (hs (f x)).symm
  refine ⟨fun U ↦ AddEquiv.ofBijective (e U) ⟨hev_inj U, hev_surj U⟩, ?_⟩
  intro U V hVU s x
  exact hev_res U V hVU s x

end TopCat
