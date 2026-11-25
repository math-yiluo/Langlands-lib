/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralCompletedScalarShift
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Completing normalized left comparisons by their adjunction mates

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-exceptional-integral-scalar-mate-completion)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u a b av bv
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Identity
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {TX : A ⥤ A} {TY : B ⥤ B}
    (q : F ⋙ TY ≅ TX ⋙ F) (beta : G ⋙ TX ⟶ TY ⋙ G)
    (hc : ∀ L, q.hom.app (G.obj L) ≫ F.map (beta.app L) ≫
      adj.counit.app (TY.obj L) = TY.map (adj.counit.app L))
    (uX : TX ≅ 𝟭 A) (uY : TY ≅ 𝟭 B)
    (hleft : ∀ K, q.hom.app K ≫ F.map (uX.hom.app K) = uY.hom.app (F.obj K))
include hc hleft in
private theorem rightIdentity (L : B) :
    beta.app L ≫ G.map (uY.hom.app L) = uX.hom.app (G.obj L) := by
  apply (adj.homEquiv _ _).symm.injective
  change F.map _ ≫ adj.counit.app _ = F.map _ ≫ adj.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  apply (cancel_epi (q.hom.app (G.obj L))).1
  calc
    _ = TY.map (adj.counit.app L) ≫ uY.hom.app L := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ uY.hom.app L) (hc L)
    _ = uY.hom.app (F.obj (G.obj L)) ≫ adj.counit.app L := uY.hom.naturality _
    _ = _ := by rw [← hleft, Category.assoc]; rfl
end Identity

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}

/-- An invertible counit transpose completes the left comparison to both adjunction
identities and all the right coherence equations.
Source: Zheng, Lemma 5.22, coefficient mate calculus.
Proof: define b as the adjunction mate of inverse q. The Mathlib mate counit formula
and q inverse identity give the counit equation. Transposing and using the triangles
gives the unit equation. Mates commute with shifts for the given adjoint shifts.
The right cocycle follows by transposing the left cocycle, using naturality and the
two counit equations. The right identity follows by the same transpose test on the
multiplication unitor. All scalar functors and their normalizations are retained.
(blueprint: lem-sf-exceptional-integral-scalar-mate-completion). -/
theorem exceptionalIntegralScalarMateCompletion
    (z : LeftMates l Ω c operation left)
    (hinv : ∀ {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a), IsIso (z.mate l Ω a ha)) :
    Nonempty (Mates l Ω c operation left) := by
  let cmp {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) : Comparison.{u} l Ω (operation s) (operation t)
        (z.scalar a ha true).functor (z.scalar a ha false).functor := by
    letI := hinv a ha
    letI := z.qShift a ha
    letI : (operation s).adjunction.CommShift ℤ :=
      ⟨(operation s).unitShift, (operation s).counitShift⟩
    letI : (operation t).adjunction.CommShift ℤ :=
      ⟨(operation t).unitShift, (operation t).counitShift⟩
    have hc (N) : (z.q a ha).hom.app ((operation s).G.obj N) ≫
        (operation t).F.map ((z.mate l Ω a ha).app N) ≫
        (operation t).adjunction.counit.app ((z.scalar a ha false).functor.obj N) =
      (z.scalar a ha false).functor.map ((operation s).adjunction.counit.app N) := by
      have h := mateEquiv_counit (operation s).adjunction (operation t).adjunction
        (z.q a ha).inv N
      change (operation t).F.map ((z.mate l Ω a ha).app N) ≫ _ = _ at h
      rw [h]
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact {
      q := z.q a ha
      b := asIso (z.mate l Ω a ha)
      unit := comparison_unit_of_counit l Ω (operation s) (operation t)
        _ _ (z.q a ha) (z.mate l Ω a ha) hc
      counit := hc
      qShift := z.qShift a ha
      bShift := NatTrans.CommShift.mateEquiv (operation s).adjunction
        (operation t).adjunction (z.q a ha).inv }
  refine ⟨{
    scalar := z.scalar
    scalarShift := z.scalarShift
    finiteScalar_eq := z.finiteScalar_eq
    finiteScalar_normalized := z.finiteScalar_normalized
    integralScalar_eq := z.integralScalar_eq
    integralScalar_normalized := z.integralScalar_normalized
    comparison := cmp
    comparison_normalized := z.q_normalized
    scalarComposition := z.scalarComposition
    cocycle := ?_
    scalarIdentity := z.scalarIdentity
    identityLeft := z.identityLeft
    identityRight := ?_
    tor_interval := z.tor_interval
    completed_shift := exceptionalIntegralCompletedScalarShift l }⟩
  · intro s t r a b d h ha hb hd
    exact ⟨z.leftCocycle a b d h ha hb hd,
      comparison_right_cocycle_of_left l Ω (cmp a ha) (cmp b hb) (cmp d hd)
        (z.scalarComposition a b d h ha hb hd true).iso
        (z.scalarComposition a b d h ha hb hd false).iso
        (z.leftCocycle a b d h ha hb hd)⟩
  · intro s a h ha N
    exact rightIdentity (operation s).adjunction (cmp a ha).q (cmp a ha).b.hom
      (cmp a ha).counit (z.scalarIdentity a h ha true).iso
      (z.scalarIdentity a h ha false).iso (z.identityLeft a h ha) N

end WeilConjectures.ExceptionalIntegralScalar
