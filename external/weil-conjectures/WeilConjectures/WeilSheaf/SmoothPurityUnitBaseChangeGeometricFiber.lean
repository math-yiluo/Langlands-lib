/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeChart
public import WeilConjectures.WeilSheaf.CondensedModelDescent
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The exceptional base change map at the unit along `k₀ ⟶ k̄`: gluing the charts (A1')

Let `k₀` be a finite field with algebraic closure `k̄`. For `X` over `k₀` we write `X̄` for its
geometric fibre, viewed over `k̄` (`geometricFiberOver`), and `h̄ : X̄ ⟶ Ȳ` for the base change
of `h : X ⟶ Y` (`geometricFiberOverMap`); the squares `πX ≫ h = h̄ ≫ πY` are cartesian
(`isPullback_geometricFiberOverMap`) and `πY = Y.hom.geometricFiberProj` is weakly étale.

Given a **global compact-support exchange** `Ex`, attached to every cartesian square over
`k₀ ⟶ k̄`, compatible with composition (`hEx`), agreeing with proper base change for the proper
pieces (`hExProper`), and with invertible mates for the étale and open-immersion pieces (step 2,
`hj`, `hg`, `hjA`, `hjV`), the exceptional base change map at the unit of a smooth `f : X ⟶ Y`
is invertible as soon as `X` is covered by charts `U --g--> A --jA--> ℙⁿ_V --p--> V --jV--> Y`
with `j ≫ f = g ≫ jA ≫ p ≫ jV` (`Chart`, the étale normal form of `f`):
`isIso_smoothUnitBaseChange_geometricFiber_of_charts`. The proof is: locality on `X̄`
(`isIso_smoothUnitBaseChange_of_openCover`), transport along `j ≫ f = g ≫ jA ≫ p ≫ jV`,
composition compatibility of `Ex`, and the chart theorem
`isIso_smoothUnitBaseChange_chart_of_projectiveSpace`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section GeometricFiber

variable {k : Type u} [Field k] [Finite k]

/-- The geometric fibre `X̄ = X ×_{k} k̄` of `X` over `k`, as an object over `k̄`. -/
abbrev geometricFiberOver (X : Over (Spec (.of k))) : Over (Spec (.of (AlgebraicClosure k))) :=
  Over.mk X.hom.geometricFiberToAlgebraicClosure

instance (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (geometricFiberOver X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))

instance (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (geometricFiberOver X).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))

instance (X : Over (Spec (.of k))) [IsSeparated X.hom] :
    IsSeparated (geometricFiberOver X).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- The base change `h̄ : X̄ ⟶ Ȳ` of a morphism `h : X ⟶ Y` over `k`. -/
abbrev geometricFiberOverMap {X Y : Over (Spec (.of k))} (h : X ⟶ Y) :
    geometricFiberOver X ⟶ geometricFiberOver Y :=
  Over.homMk (Scheme.Hom.geometricFiberMap h.left (Over.w h)) (by simp)

omit [Finite k] in
lemma geometricFiberOverMap_comp {X Y Z : Over (Spec (.of k))} (h₁ : X ⟶ Y) (h₂ : Y ⟶ Z) :
    geometricFiberOverMap (h₁ ≫ h₂) = geometricFiberOverMap h₁ ≫ geometricFiberOverMap h₂ := by
  ext1
  exact Scheme.Hom.geometricFiberMap_comp h₁.left h₂.left (Over.w h₁) (Over.w h₂)

omit [Finite k] in
/-- The base change square of `h` to `k̄` is cartesian (in the orientation of
`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`). -/
lemma isPullback_geometricFiberOverMap {X Y : Over (Spec (.of k))} (h : X ⟶ Y) :
    IsPullback X.hom.geometricFiberProj (geometricFiberOverMap h).left h.left
      Y.hom.geometricFiberProj :=
  (Scheme.Hom.isPullback_geometricFiberMap h.left (Over.w h)).flip

instance {X Y : Over (Spec (.of k))} (h : X ⟶ Y) [IsOpenImmersion h.left] :
    IsOpenImmersion (geometricFiberOverMap h).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.Hom.geometricFiberMap h.left (Over.w h)))

instance {X Y : Over (Spec (.of k))} (h : X ⟶ Y) [IsProper h.left] :
    IsProper (geometricFiberOverMap h).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) h.left (Over.w h)
    inferInstance

omit [Finite k] in
/-- The base changes of a jointly surjective family of morphisms are jointly surjective. -/
lemma exists_geometricFiberOverMap_eq {X : Over (Spec (.of k))} {ι : Type*}
    {U : ι → Over (Spec (.of k))} (j : ∀ i, U i ⟶ X)
    (hj : ∀ x : X.left, ∃ (i : ι) (y : (U i).left), (j i).left y = x)
    (x : (geometricFiberOver X).left) :
    ∃ (i : ι) (y : (geometricFiberOver (U i)).left), (geometricFiberOverMap (j i)).left y = x := by
  obtain ⟨i, y, hy⟩ := hj (X.hom.geometricFiberProj x)
  obtain ⟨z, hz, -⟩ := exists_preimage_of_isPullback
    (Scheme.Hom.isPullback_geometricFiberMap (j i).left (Over.w (j i))) x y hy.symm
  exact ⟨i, z, hz⟩

end GeometricFiber

section Charts

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

instance factPrime_ringChar_algebraicClosure : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩

instance factNe_ringChar_algebraicClosure : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- A chart of the étale normal form of `f : X ⟶ Y`: an open `j : U ⟶ X` on which
`j ≫ f = g ≫ jA ≫ p ≫ jV` with `g` étale (not recorded), `jA` an open immersion into
`P ≅ ℙⁿ_V`, `p` its projection and `jV : V ⟶ Y` an open immersion. -/
structure Chart (f : X ⟶ Y) where
  /-- The source of the chart. -/
  U : Over (Spec (.of k))
  /-- The étale target `𝔸ⁿ_V` of the chart. -/
  A : Over (Spec (.of k))
  /-- The projective space `ℙⁿ_V`. -/
  P : Over (Spec (.of k))
  /-- The open `V ⊂ Y`. -/
  V : Over (Spec (.of k))
  [hU₁ : LocallyOfFiniteType U.hom] [hU₂ : QuasiCompact U.hom] [hU₃ : IsSeparated U.hom]
  [hA₁ : LocallyOfFiniteType A.hom] [hA₂ : QuasiCompact A.hom] [hA₃ : IsSeparated A.hom]
  [hP₁ : LocallyOfFiniteType P.hom] [hP₂ : QuasiCompact P.hom] [hP₃ : IsSeparated P.hom]
  [hV₁ : LocallyOfFiniteType V.hom] [hV₂ : QuasiCompact V.hom] [hV₃ : IsSeparated V.hom]
  /-- The étale map `U ⟶ 𝔸ⁿ_V`. -/
  g : U ⟶ A
  /-- The open immersion `𝔸ⁿ_V ⟶ ℙⁿ_V`. -/
  jA : A ⟶ P
  /-- The projection `ℙⁿ_V ⟶ V`. -/
  p : P ⟶ V
  /-- The open immersion `V ⟶ Y`. -/
  jV : V ⟶ Y
  /-- The open immersion `U ⟶ X`. -/
  j : U ⟶ X
  [hj : IsOpenImmersion j.left]
  [hjV : IsOpenImmersion jV.left]
  [hp : IsProper p.left]
  /-- The relative dimension. -/
  n : ℕ
  /-- `P ≅ ℙⁿ_V`. -/
  eP : P.left ≅ ℙ(ULift.{u} (Fin (n + 1)); V.left)
  he : eP.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); V.left) ↘ V.left = p.left
  comm : j ≫ f = g ≫ jA ≫ p ≫ jV

attribute [instance] Chart.hU₁ Chart.hU₂ Chart.hU₃ Chart.hA₁ Chart.hA₂ Chart.hA₃ Chart.hP₁
  Chart.hP₂ Chart.hP₃ Chart.hV₁ Chart.hV₂ Chart.hV₃ Chart.hj Chart.hjV Chart.hp

variable (f : X ⟶ Y)

omit [Finite k] [Fact (ringChar k).Prime]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The base change of a chart: `j̄ ≫ f̄ = ḡ ≫ j̄A ≫ p̄ ≫ j̄V`. -/
lemma Chart.comm_geometricFiber (c : Chart f) :
    geometricFiberOverMap c.j ≫ geometricFiberOverMap f =
      geometricFiberOverMap c.g ≫ geometricFiberOverMap c.jA ≫ geometricFiberOverMap c.p ≫
        geometricFiberOverMap c.jV := by
  rw [← geometricFiberOverMap_comp, ← geometricFiberOverMap_comp, ← geometricFiberOverMap_comp,
    ← geometricFiberOverMap_comp, c.comm]

/-- **Gluing the charts.** Let `Ex` be a global compact-support exchange for cartesian squares
over `k₀ ⟶ k̄`, compatible with composition (`hEx`) and equal to proper base change on the
projective pieces (`hExProper`), whose mates are invertible on the open immersions `j`, `jA`,
`jV` and the étale maps `g` of a family of charts covering `X` (step 2). Then the exceptional
base change map at the unit of `f` along `k₀ ⟶ k̄` is invertible. -/
theorem isIso_smoothUnitBaseChange_geometricFiber_of_charts {ι : Type u} (c : ι → Chart f)
    (hcover : ∀ x : X.left, ∃ (i : ι) (y : (c i).U.left), (c i).j.left y = x)
    (Ex : ∀ {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
      [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
      {A' B' : Over (Spec (.of (AlgebraicClosure k)))} [LocallyOfFiniteType A'.hom]
      [QuasiCompact A'.hom] [IsSeparated A'.hom] [LocallyOfFiniteType B'.hom]
      [QuasiCompact B'.hom] [IsSeparated B'.hom] (h : A ⟶ B) (h' : A' ⟶ B')
      {πA : A'.left ⟶ A.left} {πB : B'.left ⟶ B.left}
      (_sq : IsPullback πA h'.left h.left πB),
      boundedConstructibleLowerShriek l h ⋙ boundedConstructibleUpperStarOfMap l πB ≅
        boundedConstructibleUpperStarOfMap l πA ⋙ boundedConstructibleLowerShriek l h')
    (hEx : ∀ {A B C : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
      [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      {A' B' C' : Over (Spec (.of (AlgebraicClosure k)))} [LocallyOfFiniteType A'.hom]
      [QuasiCompact A'.hom] [IsSeparated A'.hom] [LocallyOfFiniteType B'.hom]
      [QuasiCompact B'.hom] [IsSeparated B'.hom] [LocallyOfFiniteType C'.hom]
      [QuasiCompact C'.hom] [IsSeparated C'.hom]
      (h₁ : A ⟶ B) (h₂ : B ⟶ C) (h₁' : A' ⟶ B') (h₂' : B' ⟶ C')
      {πA : A'.left ⟶ A.left} {πB : B'.left ⟶ B.left} {πC : C'.left ⟶ C.left}
      (sq₁ : IsPullback πA h₁'.left h₁.left πB) (sq₂ : IsPullback πB h₂'.left h₂.left πC)
      (sq₁₂ : IsPullback πA (h₁' ≫ h₂').left (h₁ ≫ h₂).left πC),
      Ex (h₁ ≫ h₂) (h₁' ≫ h₂') sq₁₂ =
        pasteLowerShriekBaseChange l h₁ h₂ h₁' h₂' (Ex h₁ h₁' sq₁) (Ex h₂ h₂' sq₂))
    (hExProper : ∀ i, Ex (c i).p (geometricFiberOverMap (c i).p)
        (isPullback_geometricFiberOverMap (c i).p) =
      properLowerShriekBaseChangeOfMap l (c i).p (geometricFiberOverMap (c i).p)
        (isPullback_geometricFiberOverMap (c i).p))
    (eY : (boundedConstructibleUpperStarOfMap l (X := Y) (Y := geometricFiberOver Y)
      Y.hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _)
    [IsIso eY]
    (hj : ∀ i, IsIso ((upperShriekMateOfMap l (c i).j (geometricFiberOverMap (c i).j)
      (Ex (c i).j _ (isPullback_geometricFiberOverMap (c i).j))).app
        ((boundedConstructibleUpperShriek l f).obj (𝟙_ _))))
    (hg : ∀ i, IsIso ((upperShriekMateOfMap l (c i).g (geometricFiberOverMap (c i).g)
      (Ex (c i).g _ (isPullback_geometricFiberOverMap (c i).g))).app
        ((boundedConstructibleUpperShriek l ((c i).jA ≫ (c i).p ≫ (c i).jV)).obj (𝟙_ _))))
    (hjA : ∀ i, IsIso ((upperShriekMateOfMap l (c i).jA (geometricFiberOverMap (c i).jA)
      (Ex (c i).jA _ (isPullback_geometricFiberOverMap (c i).jA))).app
        ((boundedConstructibleUpperShriek l ((c i).p ≫ (c i).jV)).obj (𝟙_ _))))
    (hjV : ∀ i, IsIso (smoothUnitBaseChange l (c i).jV (geometricFiberOverMap (c i).jV)
      (Ex (c i).jV _ (isPullback_geometricFiberOverMap (c i).jV)) eY)) :
    IsIso (smoothUnitBaseChange l f (geometricFiberOverMap f)
      (Ex f _ (isPullback_geometricFiberOverMap f)) eY) := by
  -- `Ex` is compatible with equalities of morphisms
  have hExCongr : ∀ {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
      [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
      {A' B' : Over (Spec (.of (AlgebraicClosure k)))} [LocallyOfFiniteType A'.hom]
      [QuasiCompact A'.hom] [IsSeparated A'.hom] [LocallyOfFiniteType B'.hom]
      [QuasiCompact B'.hom] [IsSeparated B'.hom] {h₁ h₂ : A ⟶ B} (e : h₁ = h₂)
      {h₁' h₂' : A' ⟶ B'} (e' : h₁' = h₂') {πA : A'.left ⟶ A.left} {πB : B'.left ⟶ B.left}
      (sq₁ : IsPullback πA h₁'.left h₁.left πB) (sq₂ : IsPullback πA h₂'.left h₂.left πB),
      Ex h₂ h₂' sq₂ = transportLowerShriekBaseChange l e e' (Ex h₁ h₁' sq₁) := by
    intro A B _ _ _ _ _ _ A' B' _ _ _ _ _ _ h₁ h₂ e h₁' h₂' e' πA πB sq₁ sq₂
    subst e e'
    ext K
    simp [transportLowerShriekBaseChange]
  refine isIso_smoothUnitBaseChange_of_openCover l f (geometricFiberOverMap f)
    (Ex f _ (isPullback_geometricFiberOverMap f)) eY (fun i ↦ (c i).j)
    (fun i ↦ geometricFiberOverMap (c i).j)
    (fun i ↦ Ex (c i).j _ (isPullback_geometricFiberOverMap (c i).j))
    (exists_geometricFiberOverMap_eq (fun i ↦ (c i).j) hcover) hj fun i ↦ ?_
  -- the restriction to the chart `U`, through `j ≫ f = g ≫ jA ≫ p ≫ jV`
  have sqjf := (isPullback_geometricFiberOverMap (c i).j).paste_vert
    (isPullback_geometricFiberOverMap f)
  rw [← hEx (c i).j f _ _ (isPullback_geometricFiberOverMap (c i).j)
    (isPullback_geometricFiberOverMap f) sqjf]
  have sqpV := (isPullback_geometricFiberOverMap (c i).p).paste_vert
    (isPullback_geometricFiberOverMap (c i).jV)
  have sqApV := (isPullback_geometricFiberOverMap (c i).jA).paste_vert sqpV
  have sqchart := (isPullback_geometricFiberOverMap (c i).g).paste_vert sqApV
  rw [hExCongr (c i).comm.symm (c i).comm_geometricFiber.symm sqchart sqjf,
    isIso_smoothUnitBaseChange_transport_iff,
    hEx (c i).g _ _ _ (isPullback_geometricFiberOverMap (c i).g) sqApV sqchart,
    hEx (c i).jA _ _ _ (isPullback_geometricFiberOverMap (c i).jA) sqpV sqApV,
    hEx (c i).p _ _ _ (isPullback_geometricFiberOverMap (c i).p)
      (isPullback_geometricFiberOverMap (c i).jV) sqpV,
    hExProper i]
  have := hg i
  have := hjA i
  have := hjV i
  exact isIso_smoothUnitBaseChange_chart_of_projectiveSpace l (c i).g (c i).jA (c i).p (c i).jV
    (geometricFiberOverMap (c i).g) (geometricFiberOverMap (c i).jA)
    (geometricFiberOverMap (c i).p) (geometricFiberOverMap (c i).jV)
    (Ex (c i).g _ (isPullback_geometricFiberOverMap (c i).g))
    (Ex (c i).jA _ (isPullback_geometricFiberOverMap (c i).jA))
    (Ex (c i).jV _ (isPullback_geometricFiberOverMap (c i).jV)) eY
    (isPullback_geometricFiberOverMap (c i).p)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap l (X := (c i).V)
      (Y := geometricFiberOver (c i).V)
      (c i).V.hom.geometricFiberProj)).inv (c i).n (c i).eP (c i).he

end Charts

end AlgebraicGeometry.ProEtale.CondensedRing
