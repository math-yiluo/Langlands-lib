/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting

/-! # Open base-change component isomorphism
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-construction/sec-construction-of-rf/sk-thm-sf-comp-composition/
det-sf-comp-composition-base-change.md,
Clause (1); proof (1), first sentence: the common right adjoint
`u_* j'^* ≅ j^* a_*` and its section normalization.
(blueprint: stage3-sfb-open-base-change-component-mono)
-/
set_option autoImplicit false
@[expose] public section
universe u
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

/-- The canonical mate comparison for open base change of condensed module objects.
Source: blueprint proof (1), first sentence: the common right adjoint and its
section normalization (blueprint: stage3-sfb-open-base-change-component-mono).

The mate is formed from the specified upper-star compositors and the pullback
square; it is the actual natural isomorphism used by the normalized section formula. -/
noncomputable def openBaseChangeCanonical
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z Z' : Scheme.{u}} (j : X ⟶ Z) (a : Z' ⟶ Z)
    [IsOpenImmersion j] :
    (lowerStar Λ a ⋙ upperStar Λ j) ⟶
      (upperStar Λ (pullback.fst a j) ⋙ lowerStar Λ (pullback.snd a j)) :=
  (mateEquiv (upperStarLowerStarAdjunction Λ a)
      (upperStarLowerStarAdjunction Λ (pullback.snd a j))
      (TwoSquare.mk _ _ _ _
        (((upperStarComp Λ (pullback.fst a j) a).symm ≪≫
          upperStarCongr Λ (IsPullback.of_hasPullback a j).w ≪≫
          upperStarComp Λ (pullback.snd a j) j).inv)))

/-- The open base-change mate has the canonical section normalization.
Source: blueprint proof (1), first sentence: the common right adjoint and its
section normalization (blueprint: stage3-sfb-open-base-change-component-mono).
The coprojections and section arrow are the specified module constructions, so
the displayed equation fixes the mate rather than allowing arbitrary section isos.

Proof (node stage3-sfb-open-base-change-component-mono, to be formalized at stage 3):
1. Pass to sectionwise module sheaves (def-weil-pbc-internal-abelian-sheaf-module-equivalence).
   The coefficient maps `α_f` of lemma-inverse-image-coefficient-sheaves--1 are ring isomorphisms,
   and extension of scalars along each is restriction along its inverse
   (def-sfb-modobj-extension-along-iso); so `upperStar`/`lowerStar` are the ringed-site
   inverse and direct images over the canonically identified coefficient rings.
2. Apply lem-sfb-proetale-open-restriction-counit with `f = a`, `h = j`, `g = j'`,
   `f_W = u` and `R = Λ_Z`, regarding `N` as an `a⁻¹Λ_Z`-module along `α_a`; it gives
   `j⁻¹a_*N ≅ u_*j'⁻¹N`, transported back through step 1 to `j^*a_*N ≅ u_*j'^*N`,
   with no qcqs, field or finiteness hypothesis.
3. Its evaluation formula `N(Z' ×_Z V) ≅ N(X' ×_X V)` is, after swapping factors, the
   restriction along `sectionArrow`; both coprojections are bijective for the open
   immersions `j`, `j'`. Naturality in `V` follows from the fibre-product universal
   property, naturality in `N` by definition, and linearity because the scalar
   identifications are restrictions along ring isomorphisms. -/
theorem openBaseChangeComponentIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z Z' : Scheme.{u}} (j : X ⟶ Z) (a : Z' ⟶ Z)
    [IsOpenImmersion j]
    (N : Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj Λ Z')) :
    IsIso (openBaseChangeCanonical Λ j a) ∧
    (∀ E : X.ProEt,
      Function.Bijective
        (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ a).obj N) E)) ∧
    (∀ E : X.ProEt,
      Function.Bijective
        (ModuleOpenPasting.coprojection Λ (pullback.fst a j) N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
            (pullback.snd a j)).obj E))) ∧
    ∀ (E : X.ProEt)
      (s : N.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
        ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))),
      ((openBaseChangeCanonical Λ j a).app N).hom.hom.app (op E)
          (ModuleOpenPasting.coprojection Λ j ((lowerStar Λ a).obj N) E s) =
        ModuleOpenPasting.coprojection Λ (pullback.fst a j) N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
            (pullback.snd a j)).obj E)
          (N.X.obj.map
            (ModuleOpenPasting.sectionArrow a j (pullback.snd a j)
              (pullback.fst a j) (IsPullback.of_hasPullback a j) E).op s) := by
  obtain ⟨β, hsec, _, _, _, _, _, hcan⟩ :=
    ModuleOpenPasting.moduleDirectImageOpenPasting_canonical Λ
  have hb :
      (β a j (pullback.snd a j) (pullback.fst a j)
        (IsPullback.of_hasPullback a j)).hom = openBaseChangeCanonical Λ j a :=
    hcan a j (pullback.snd a j) (pullback.fst a j) (IsPullback.of_hasPullback a j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hb]
    infer_instance
  · exact hsec.1 j ((lowerStar Λ a).obj N)
  · intro E
    exact hsec.1 (pullback.fst a j) N
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.snd a j)).obj E)
  · intro E s
    rw [← hb]
    exact hsec.2 a j (pullback.snd a j) (pullback.fst a j)
      (IsPullback.of_hasPullback a j) N E s

end AlgebraicGeometry.ProEtale.CondensedRing
