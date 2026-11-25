/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-! # Small indices for ind-étale presentations

Source: the universe reduction in the final paragraph of the continuity-map detail,
sec-proetale-coefficients/sk-def-pe-classical-definition.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

private theorem etale_precomp :
    CommRingCat.etale.{u}.HasOfPrecompProperty CommRingCat.etale := by
  constructor
  intro R S T f g hf hfg
  change RingHom.Etale g.hom
  have hf' : RingHom.Etale f.hom := hf
  have hfg' : RingHom.Etale (g.hom.comp f.hom) := hfg
  algebraize [f.hom, g.hom, g.hom.comp f.hom]
  let : Algebra.Etale R S := hf'
  let : Algebra.Etale R T := hfg'
  exact Algebra.Etale.of_restrictScalars R S T

attribute [local instance] etale_precomp

private theorem ind_retract {C : Type*} [Category C] [LocallySmall.{u} C]
    {P : ObjectProperty C} (hP : P ≤ ObjectProperty.isFinitelyPresentable.{u} C)
    {B D : C} (s : B ⟶ D) (p : D ⟶ B) (hsp : s ≫ p = 𝟙 B)
    (hD : ObjectProperty.ind.{u} P D) : ObjectProperty.ind.{u} P B := by
  let e := p ≫ s
  have he : e ≫ e = e := by
    calc
      e ≫ e = p ≫ (s ≫ p) ≫ s := by simp only [e, Category.assoc]
      _ = e := by rw [hsp]; simp [e]
  let F : ℕ ⥤ C := Functor.ofSequence (X := fun _ ↦ D) (fun _ ↦ e)
  let c : Cocone F :=
    { pt := B
      ι := NatTrans.ofSequence (fun _ ↦ p) (by
        intro n
        simp [F, Functor.ofSequence_map_homOfLE_succ, e, Category.assoc, hsp]) }
  have eqn (a : Cocone F) (n : ℕ) : e ≫ a.ι.app (n + 1) = a.ι.app n := by
    simpa [F, Functor.ofSequence_map_homOfLE_succ] using
      a.w (homOfLE (Nat.le_add_right n 1))
  have stable (a : Cocone F) (n : ℕ) : e ≫ a.ι.app n = a.ι.app n := by
    rw [← eqn a n, ← Category.assoc, he]
  have same (a : Cocone F) (n : ℕ) : a.ι.app n = a.ι.app 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← stable a (n + 1), eqn a n, ih]
  have hc : IsColimit c :=
    { desc a := s ≫ a.ι.app 0
      fac a n := by
        change p ≫ s ≫ a.ι.app 0 = a.ι.app n
        rw [← Category.assoc, stable a 0, same a n]
      uniq a m hm := by
        have hm0 := hm 0
        change p ≫ m = a.ι.app 0 at hm0
        rw [← hm0, ← Category.assoc, hsp, Category.id_comp] }
  rw [← ObjectProperty.ind_ind hP]
  apply ObjectProperty.of_essentiallySmall_index.{u} (⟨F, c.ι, hc⟩ : ColimitPresentation ℕ B)
  intro n
  exact hD

set_option backward.defeqAttrib.useBackward true in
/-- A filtered étale presentation with a larger index admits a small presentation.
Source: the final paragraph of the continuity-map detail and its finite-presentation
universe reduction (auxiliary; not a blueprint node).

Proof: Fix a universe-u map R → B and its larger filtered presentation. Let E be the
category of finitely presented étale R-algebras equipped with a map to B. Finite
presentations and their maps into B give E a universe-u skeleton. E has finite
colimits: the initial object is R, coproducts are tensor products, and coequalizers
are étale quotients. For the last assertion, the equalizer of two maps between affine
étale R-schemes is the pullback of an affine étale diagonal; that diagonal is both
open and closed, so the equalizer is again affine étale. These constructions retain
the maps to B. Thus E is filtered. Form its small ring colimit C, an ind-étale
R-algebra, with the canonical map p : C → B.

The original stages and their maps to B define objects of E, hence a compatible
cocone to C. The given large colimit property supplies s : B → C. On every original
stage p ∘ s is the given map to B, so p ∘ s = id. All maps respect R because the
nonempty index supplies a stage. Consequently B is a retract of C as an R-algebra.
A retract of an ind-étale algebra is ind-étale: if e = s ∘ p, the countable diagram
C --e--> C --e--> ... has colimit B, with projections p. Indeed a cocone with
components a_n satisfies a_n = a_(n+1) e; idempotence implies a_n e = a_n and then
all a_n coincide, and a_0 s is the unique factorization through p. Countable
filtered colimits of ind-étale algebras are ind-étale by flattening their small
presentations (ObjectProperty.ind_ind, using finite presentation of étale algebras).
This gives a universe-u presentation of B. The argument also includes zero rings
and empty spectra: the zero algebra is étale and the indexing category has the
initial object R, so neither nonemptiness nor the coequalizer argument excludes them. -/
theorem CommRingCat.ind_etale_small_index :
    MorphismProperty.ind.{u + 1} CommRingCat.etale.{u} ≤
      MorphismProperty.ind.{u} CommRingCat.etale.{u} := by
  intro R B f hf
  rw [MorphismProperty.ind_iff_ind_underMk] at hf ⊢
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  let V := MorphismProperty.Under.forget CommRingCat.etale ⊤ R
  let E := CostructuredArrow V (Under.mk f)
  let H : E ⥤ Under R := CostructuredArrow.proj V (Under.mk f) ⋙ V
  have : HasFiniteColimits E := inferInstance
  have : IsFiltered E := IsFiltered.of_hasFiniteColimits E
  have : EssentiallySmall.{u} E := inferInstance
  have : FinallySmall.{u} E := finallySmall_of_essentiallySmall E
  have : HasColimitsOfShape E (Under R) :=
    hasColimitsOfShape_of_finallySmall E (Under R)
  have : HasColimit H := inferInstance
  let lift : J ⥤ E :=
    { obj j := CostructuredArrow.mk
        (Y := MorphismProperty.Under.mk ⊤ (pres.diag.obj j).hom (hpres j))
        (pres.ι.app j)
      map {i j} a := CostructuredArrow.homMk
        (MorphismProperty.Under.homMk (pres.diag.map a).right (Under.w _))
        (pres.ι.naturality a) }
  let cc : Cocone H :=
    { pt := Under.mk f
      ι := { app j := j.hom
             naturality {i j} a := by
               change V.map a.left ≫ j.hom = i.hom
               exact a.w } }
  let p : colimit H ⟶ Under.mk f := colimit.desc H cc
  let s : Under.mk f ⟶ colimit H :=
    pres.isColimit.desc ((colimit.cocone H).whisker lift)
  have hsp : s ≫ p = 𝟙 _ := by
    apply pres.isColimit.hom_ext
    intro j
    dsimp [s]
    rw [← Category.assoc, pres.isColimit.fac]
    exact colimit.ι_desc cc (lift.obj j)
  have hC : ObjectProperty.ind.{u} CommRingCat.etale.underObj (colimit H) := by
    apply ObjectProperty.of_essentiallySmall_index
      (⟨H, (colimit.cocone H).ι, colimit.isColimit H⟩ : ColimitPresentation E (colimit H))
    intro j
    exact j.left.prop
  apply ind_retract (P := CommRingCat.etale.underObj) ?_ s p hsp hC
  intro Z hZ
  have hz := CommRingCat.etale_le_isFinitelyPresentable Z.hom hZ
  exact hz
