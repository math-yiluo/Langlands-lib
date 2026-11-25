/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # Normalized compact-support scalar cocycles at ring stages

Source: current Weil blueprint, exceptional inverse image coefficient normalization;
Stacks Project, Tags 0GL1, 0D6D and 0E47
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle).

The input records below package only the realizations stipulated in the statement.
The categories, full inclusions, scalar associators, multiplication units and proper/open
comparison are the existing constructions. In particular no preservation or invertibility
of an ambient proper mate is built into these records.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.ConstructibleExceptionalCoefficients
open WeilConjectures.PurCompactSupport

namespace WeilConjectures.NormalizedRingCompactScalar

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{max u v}} {f : X ⟶ Y} (c : Compactification f)

/-- A supplied compact-support functor and its specified ambient realization.
Source: blueprint exceptional coefficient normalization, realization paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Support (s : RingStage.{max u v} l) where
  functor : C.{u, v} l Ω X (s.stage l) ⥤ C.{u, v} l Ω Y (s.stage l)
  realization : functor ⋙ RingStage.inclusion.{u, v} l Ω Y s ≅
    RingStage.inclusion.{u, v} l Ω X s ⋙ image (s.coefficients l) c

/-- A supplied scalar functor with its actual ordinary derived scalar realization.
No exactness or shift structure is an additional input.
Source: blueprint exceptional coefficient normalization, sigma paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Scalar {s t : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{max u v}) where
  functor : C.{u, v} l Ω T (s.stage l) ⥤ C.{u, v} l Ω T (t.stage l)
  realization : functor ⋙ RingStage.inclusion.{u, v} l Ω T t ≅
    RingStage.inclusion.{u, v} l Ω T s ⋙ pbcDerivedExtend (a.map T)

/-- The written normalization of the supplied restricted comparison, component by component.
Source: blueprint exceptional coefficient normalization, displayed realization equation
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
def Normalized {s t : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (t.coefficients l))
    (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t)
    (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
    (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor) : Prop :=
  ∀ K : C.{u, v} l Ω X (s.stage l),
    (RingStage.inclusion.{u, v} l Ω Y t).map (q.hom.app K) ≫
        B.realization.hom.app (AX.functor.obj K) ≫
        (image (t.coefficients l) c).map (AX.realization.hom.app K) =
      AY.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (A.realization.hom.app K) ≫
        (comparison a c).app ((RingStage.inclusion.{u, v} l Ω X s).obj K)

/-- A supplied restricted associator whose realization is balanced tensor associativity.
Source: blueprint exceptional coefficient normalization, alpha paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Associator {s t r : RingStage.{max u v} l}
    {a : Change (s.coefficients l) (t.coefficients l)}
    {b : Change (t.coefficients l) (r.coefficients l)}
    {d : Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
    (T : Scheme.{max u v}) (A : Scalar.{u, v} l Ω a T) (B : Scalar.{u, v} l Ω b T)
    (D : Scalar.{u, v} l Ω d T) where
  iso : A.functor ⋙ B.functor ≅ D.functor
  normalized (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T r).map (iso.hom.app K) ≫ D.realization.hom.app K =
      B.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (b.map T)).map (A.realization.hom.app K) ≫
        (tensorComposition (a.map T) (b.map T) (d.map T) (h T)).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K)

/-- A supplied restricted unit whose realization is scalar multiplication.
The equality h retains arbitrary presentations of the identity ring map.
Source: blueprint exceptional coefficient normalization, unit paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Unit {s : RingStage.{max u v} l}
    {a : Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _) (T : Scheme.{max u v})
    (A : Scalar.{u, v} l Ω a T) where
  iso : A.functor ≅ 𝟭 _
  normalized (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T s).map (iso.hom.app K) =
      A.realization.hom.app K ≫
        (eqToIso (congrArg pbcDerivedExtend (h T))).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K) ≫
        (tensorIdentity ((s.coefficients l).ring T)).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K)

/-- All five clauses of the normalized ring compact-support scalar assertion.
The last clause expresses independence of an allowedness proof through uniqueness for
fixed actual maps and realizations; any alternate presentation is compared via those
realizations. All coefficient changes are compatible maps of the actual ring sheaves.
Source: blueprint exceptional coefficient normalization, ambient and restricted cocycles
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Laws : Prop where
  ambient_composition {s t r : RingStage.{max u v} l}
      (a : Change (s.coefficients l) (t.coefficients l))
      (b : Change (t.coefficients l) (r.coefficients l))
      (d : Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
      (M : DerivedCategory (pbcModules X ((s.coefficients l).ring X))) :
    (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image (r.coefficients l) c).map
          ((tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((image (s.coefficients l) c).obj M) ≫ (comparison d c).app M
  ambient_identity {s : RingStage.{max u v} l}
      (a : Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _)
      (M : DerivedCategory (pbcModules X ((s.coefficients l).ring X))) :
    (comparison a c).app M ≫ (image (s.coefficients l) c).map
        ((eqToIso (congrArg pbcDerivedExtend (h X)) ≪≫
          tensorIdentity ((s.coefficients l).ring X)).hom.app M) =
      (eqToIso (congrArg pbcDerivedExtend (h Y)) ≪≫
        tensorIdentity ((s.coefficients l).ring Y)).hom.app
          ((image (s.coefficients l) c).obj M)
  composition {s t r : RingStage.{max u v} l}
      (a : Change (s.coefficients l) (t.coefficients l))
      (b : Change (t.coefficients l) (r.coefficients l))
      (d : Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
      (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t) (D : Support.{u, v} l Ω c r)
      (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
      (BX : Scalar.{u, v} l Ω b X) (BY : Scalar.{u, v} l Ω b Y)
      (DX : Scalar.{u, v} l Ω d X) (DY : Scalar.{u, v} l Ω d Y)
      (qa : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
      (qb : B.functor ⋙ BY.functor ≅ BX.functor ⋙ D.functor)
      (qd : A.functor ⋙ DY.functor ≅ DX.functor ⋙ D.functor)
      (ha : Normalized.{u, v} l Ω c a A B AX AY qa)
      (hb : Normalized.{u, v} l Ω c b B D BX BY qb)
      (hd : Normalized.{u, v} l Ω c d A D DX DY qd)
      (αX : Associator.{u, v} l Ω h X AX BX DX) (αY : Associator.{u, v} l Ω h Y AY BY DY)
      (K : C.{u, v} l Ω X (s.stage l)) :
    BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
        D.functor.map (αX.iso.hom.app K) =
      αY.iso.hom.app (A.functor.obj K) ≫ qd.hom.app K
  identity {s : RingStage.{max u v} l} (a : Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _) (A : Support.{u, v} l Ω c s)
      (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
      (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ A.functor)
      (hq : Normalized.{u, v} l Ω c a A A AX AY q)
      (uX : Unit.{u, v} l Ω h X AX) (uY : Unit.{u, v} l Ω h Y AY)
      (K : C.{u, v} l Ω X (s.stage l)) :
    q.hom.app K ≫ A.functor.map (uX.iso.hom.app K) = uY.iso.hom.app (A.functor.obj K)
  unique {s t : RingStage.{max u v} l} (a : Change (s.coefficients l) (t.coefficients l))
      (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t)
      (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
      (q q' : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
      (hq : Normalized.{u, v} l Ω c a A B AX AY q)
      (hq' : Normalized.{u, v} l Ω c a A B AX AY q') : q = q'

private theorem inclusionFaithful (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).Faithful := by
  cases s <;> dsimp only [RingStage.inclusion] <;> infer_instance

-- Transport a normalized unit square through faithful realization, abstractly.
private theorem identityTransport {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (I₁ : C₁ ⥤ D₁) (I₂ : C₂ ⥤ D₂) [I₂.Faithful]
    (F : C₁ ⥤ C₂) (TX : C₁ ⥤ C₁) (TY : C₂ ⥤ C₂)
    (H : D₁ ⥤ D₂) (SX : D₁ ⥤ D₁) (SY : D₂ ⥤ D₂)
    (eF : F ⋙ I₂ ≅ I₁ ⋙ H) (eX : TX ⋙ I₁ ≅ I₁ ⋙ SX)
    (eY : TY ⋙ I₂ ≅ I₂ ⋙ SY) (q : F ⋙ TY ≅ TX ⋙ F)
    (uX : TX ≅ 𝟭 _) (uY : TY ≅ 𝟭 _) (vX : SX ≅ 𝟭 _) (vY : SY ≅ 𝟭 _)
    (Q : H ⋙ SY ⟶ SX ⋙ H)
    (hq : ∀ K, I₂.map (q.hom.app K) ≫ eF.hom.app (TX.obj K) ≫
      H.map (eX.hom.app K) = eY.hom.app (F.obj K) ≫
        SY.map (eF.hom.app K) ≫ Q.app (I₁.obj K))
    (hX : ∀ K, I₁.map (uX.hom.app K) = eX.hom.app K ≫ vX.hom.app (I₁.obj K))
    (hY : ∀ K, I₂.map (uY.hom.app K) = eY.hom.app K ≫ vY.hom.app (I₂.obj K))
    (hQ : ∀ M, Q.app M ≫ H.map (vX.hom.app M) = vY.hom.app (H.obj M))
    (K : C₁) : q.hom.app K ≫ F.map (uX.hom.app K) = uY.hom.app (F.obj K) := by
  apply I₂.map_injective
  apply (Iso.cancel_iso_hom_right _ _ (eF.app K)).1
  have hn := eF.hom.naturality (uX.hom.app K)
  have hv := vY.hom.naturality (eF.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  dsimp only [Functor.id_map, Functor.comp_obj] at hv
  simp only [Functor.map_comp, Iso.app_hom, Category.assoc]
  rw [hn, hX K]
  simp only [Functor.map_comp]
  rw [reassoc_of% (hq K), hQ (I₁.obj K), hv, hY (F.obj K), Category.assoc]

universe w

-- An identity presentation can be replaced by the actual identity change.
private def identityChange (R : Coefficients.{w}) : Change R R where
  map W := 𝟙 (R.ring W)
  square g := by
    rw [Category.comp_id, (proEtaleSheafInverseImage g CommRingCat.{w + 1}).map_id,
      Category.id_comp]

private theorem change_eq_identity (R : Coefficients.{w}) (a : Change R R)
    (h : ∀ W, a.map W = 𝟙 (R.ring W)) : a = identityChange R := by
  cases a with
  | mk m square =>
    have hm : m = fun W ↦ 𝟙 (R.ring W) := funext h
    cases hm
    rfl

private theorem compositionProof {s t r : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (t.coefficients l))
    (b : Change (t.coefficients l) (r.coefficients l))
    (d : Change (s.coefficients l) (r.coefficients l))
    (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
    (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t) (D : Support.{u, v} l Ω c r)
    (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
    (BX : Scalar.{u, v} l Ω b X) (BY : Scalar.{u, v} l Ω b Y)
    (DX : Scalar.{u, v} l Ω d X) (DY : Scalar.{u, v} l Ω d Y)
    (qa : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
    (qb : B.functor ⋙ BY.functor ≅ BX.functor ⋙ D.functor)
    (qd : A.functor ⋙ DY.functor ≅ DX.functor ⋙ D.functor)
    (ha : Normalized.{u, v} l Ω c a A B AX AY qa)
    (hb : Normalized.{u, v} l Ω c b B D BX BY qb)
    (hd : Normalized.{u, v} l Ω c d A D DX DY qd)
    (αX : Associator.{u, v} l Ω h X AX BX DX) (αY : Associator.{u, v} l Ω h Y AY BY DY)
    (K : C.{u, v} l Ω X (s.stage l)) :
  BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
      D.functor.map (αX.iso.hom.app K) =
    αY.iso.hom.app (A.functor.obj K) ≫ qd.hom.app K := by
  let _ := inclusionFaithful l Ω Y r
  apply (RingStage.inclusion.{u, v} l Ω Y r).map_injective
  let e := D.realization.app (DX.functor.obj K) ≪≫
    (image (r.coefficients l) c).mapIso (DX.realization.app K)
  apply (Iso.cancel_iso_hom_right _ _ e).1
  dsimp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  have hnD := D.realization.hom.naturality (αX.iso.hom.app K)
  have hnBY := BY.realization.hom.naturality (qa.hom.app K)
  have hnQ := (comparison b c).naturality (AX.realization.hom.app K)
  have hnτ := (tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.naturality
    (A.realization.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnD hnBY hnQ hnτ
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnD, ← (image (r.coefficients l) c).map_comp,
    αX.normalized K]
  simp only [Functor.map_comp]
  rw [reassoc_of% (hb (AX.functor.obj K)), reassoc_of% hnBY,
    ← reassoc_of% hnQ]
  rw [← (pbcDerivedExtend (b.map Y)).map_comp_assoc,
    ← (pbcDerivedExtend (b.map Y)).map_comp_assoc, Category.assoc, ha K]
  simp only [Functor.map_comp, Category.assoc]
  rw [comparison_composition a b d h c
    ((RingStage.inclusion.{u, v} l Ω X s).obj K)]
  rw [hd K, reassoc_of% (αY.normalized (A.functor.obj K)),
    ← reassoc_of% hnτ]

private theorem identityProof {s : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (s.coefficients l))
    (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _) (A : Support.{u, v} l Ω c s)
    (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
    (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ A.functor)
    (hq : Normalized.{u, v} l Ω c a A A AX AY q)
    (uX : Unit.{u, v} l Ω h X AX) (uY : Unit.{u, v} l Ω h Y AY)
    (K : C.{u, v} l Ω X (s.stage l)) :
  q.hom.app K ≫ A.functor.map (uX.iso.hom.app K) = uY.iso.hom.app (A.functor.obj K) := by
  have ha := change_eq_identity (s.coefficients l) a h
  subst a
  let _ := inclusionFaithful l Ω Y s
  apply identityTransport (RingStage.inclusion.{u, v} l Ω X s)
    (RingStage.inclusion.{u, v} l Ω Y s) A.functor AX.functor AY.functor
    (image (s.coefficients l) c) (pbcDerivedExtend (𝟙 ((s.coefficients l).ring X)))
    (pbcDerivedExtend (𝟙 ((s.coefficients l).ring Y)))
    A.realization AX.realization AY.realization q uX.iso uY.iso
    (tensorIdentity ((s.coefficients l).ring X))
    (tensorIdentity ((s.coefficients l).ring Y))
    (comparison (identityChange (s.coefficients l)) c) hq ?_ ?_ ?_ K
  · intro L
    have hu := uX.normalized L
    simp only [identityChange, eqToIso_refl, Iso.refl_hom, NatTrans.id_app] at hu
    have hi := Category.id_comp
      ((tensorIdentity ((s.coefficients l).ring X)).hom.app
        ((RingStage.inclusion.{u, v} l Ω X s).obj L))
    exact hu.trans (congrArg (fun k ↦ AX.realization.hom.app L ≫ k) hi)
  · intro L
    have hu := uY.normalized L
    simp only [identityChange, eqToIso_refl, Iso.refl_hom, NatTrans.id_app] at hu
    have hi := Category.id_comp
      ((tensorIdentity ((s.coefficients l).ring Y)).hom.app
        ((RingStage.inclusion.{u, v} l Ω Y s).obj L))
    exact hu.trans (congrArg (fun k ↦ AY.realization.hom.app L ≫ k) hi)
  · intro M
    simpa only [eqToIso_refl, Iso.refl_trans] using
      comparison_identity (identityChange (s.coefficients l)) (fun _ ↦ rfl) c M

private theorem uniqueProof {s t : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (t.coefficients l))
    (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t)
    (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
    (q q' : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
    (hq : Normalized.{u, v} l Ω c a A B AX AY q)
    (hq' : Normalized.{u, v} l Ω c a A B AX AY q') : q = q' := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let _ := inclusionFaithful l Ω Y t
  apply (RingStage.inclusion.{u, v} l Ω Y t).map_injective
  let e := B.realization.app (AX.functor.obj K) ≪≫
    (image (t.coefficients l) c).mapIso (AX.realization.app K)
  apply (Iso.cancel_iso_hom_right _ _ e).1
  dsimp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  exact (hq K).trans (hq' K).symm

private theorem allLaws : Laws.{u, v} l Ω c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s t r a b d h M
    exact comparison_composition a b d h c M
  · intro s a h M
    have ha := change_eq_identity (s.coefficients l) a h
    subst a
    simpa only [eqToIso_refl, Iso.refl_trans] using
      comparison_identity (identityChange (s.coefficients l)) (fun _ ↦ rfl) c M
  · exact compositionProof.{u, v} l Ω c
  · exact identityProof.{u, v} l Ω c
  · exact uniqueProof.{u, v} l Ω c

/-- Normalized compact-support scalar comparisons obey the ambient and restricted cocycles.
Source: current blueprint, exceptional inverse image coefficient normalization;
Stacks Project, Tags 0GL1, 0D6D, 0E47
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle).

Proof:
1. Write J_s for open extension and P_s for proper direct image. Open tensor
normalization identifies the restriction of each beta with identity. Restrict the
successive and direct beta composites to the open. Coefficient pullback coherence
identifies both with balanced associativity. Full faithfulness of J_r detects equality.
Multiplication units give the same open identity law. No flatness or stalk detection
is involved, including for completed ring sheaves.
2. Apply the ringed coefficient projection cocycle to the proper factor and the three
ring sheaves, using the compatible pull identifications. Its chi is the specified
proper mate. It supplies associativity and multiplication identities without assuming
invertibility, so quotient and mixed integral/finite maps are included.
3. Substitute Q_a = P_t(beta_a) chi_a(J_s). Naturality of chi_b at beta_a moves
P_t(beta_a) across chi_b. Functoriality followed by the open identity of step 1 and
the proper identity of step 2 yields the ambient composition identity. Apply their
unit identities in the same order for ambient_identity.
4. For the restricted comparisons put A_a = H_t(sigma_a^X) r_t(T_a^X) and
B_a = S_a^Y(r_s) sigma_a^Y(F_s). The hypothesis is A_a I_t(q_a) = Q_a(I_s) B_a.
Substitute this first for q_b and then q_a. Naturality of sigma_b^Y at q_a and of Q_b
at sigma_a^X identifies the successive realized comparison with Q_b S_b(Q_a),
conjugated by the successive A and B isomorphisms.
5. The two Associator.normalized equations and naturality of r_r identify the realized
restricted associators with tau_X and tau_Y. Apply the ambient composition identity,
cancel the A_d isomorphism and use faithfulness of the full inclusion I_r to obtain
composition at every K.
6. Unit.normalized, naturality of r_s and of scalar multiplication turn the identity
normalization into the ambient unit equation. Cancel r_s and use faithfulness for
identity. Finally Normalized determines I_t(q_a) uniquely by cancelling A_a. Faithfulness
and extensionality give unique. There is no inverse of the ambient Q_a anywhere.
-/
theorem normalizedRingCompactScalarCocycle
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Laws.{u, v} l Ω c := by
  exact (fun _ : l ≠ D.p ↦ allLaws l Ω c) hl

end WeilConjectures.NormalizedRingCompactScalar
