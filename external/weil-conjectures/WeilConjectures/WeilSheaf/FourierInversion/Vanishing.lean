/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.TraceFunctionTensor
public import WeilConjectures.WeilSheaf.TraceFunctionVanishing

/-!
# Fourier inversion: relative vanishing

The compactly supported direct image of `ℒ_ψ(a s) ⊗ π^* P` along a trivial line bundle
`π` with fibre coordinate `s` vanishes, for `a` a unit and `ψ` nontrivial (blueprint
`lemma-integral-linear-character--2`).

## Proof

Write `K = ℒ_ψ(a s) ⊗ π^* P` and `M = Rπ₀! K`. Translation invariance: over `Y` itself, with
`Y ×_X Y` the line bundle with fibre coordinates `(s₁, s₂)`, compact-support base change gives
`π^* M ≅ Rq₂₀!(q₁^* K)`. The shear `τ : (s₁, s₂) ↦ (s₁ + a⁻¹ s₂, s₂)` is an automorphism over
the second factor, and `τ^* q₁^* K ≅ ℒ_ψ(s₂) ⊗ q₁^* K` by the multiplicativity
`ℒ_ψ(a s₁ + s₂) ≅ ℒ_ψ(s₂) ⊗ ℒ_ψ(a s₁)`. Base change along `τ` and the projection formula give

`π^* M ≅ ℒ_ψ(s) ⊗ π^* M`.

On trace functions of the cohomology sheaves `𝓗ʲ(M)` this says
`t_{𝓗ʲ M}(x) = ψ(Tr c) t_{𝓗ʲ M}(x)` for every `𝔽_{qⁿ}`-point `x` of `X` and every `c ∈ 𝔽_{qⁿ}`;
choosing `c` with `ψ(Tr c) ≠ 1` gives `t_{𝓗ʲ M} = 0`, hence `𝓗ʲ M = 0`
(`AlgebraicGeometry.WeilSheaf.isZero_of_traceFunction_eq_zero`) and `M = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Pullbacks of Weil complexes along equal morphisms are isomorphic. -/
lemma WeilComplex.nonempty_upperStar_iso_of_eq {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] {f g : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] (h : f = g) :
    Nonempty (WeilComplex.upperStar (k₀ := k₀) (l := l) f ≅ WeilComplex.upperStar g) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- The trace function of the Artin–Schreier sheaf `ℒ_{ψ,f}` of a function `f` at an
`𝔽_{qⁿ}`-rational point `y` is `ψ(Tr(f(y)))`. -/
theorem WeilSheaf.traceFunction_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) (f : Γ(X, ⊤))
    {n : ℕ} (hn : n ≠ 0)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (artinSchreierOf ψ f).traceFunction n y =
      ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
        ((Scheme.ΓSpecIso (.of (FiniteField.galoisExtension k₀ n))).hom.hom (y.1.appTop f))) := by
  have h : (y.1 ≫ affineLine.homOfSection k₀ f).appTop (AffineSpace.coord _ PUnit.unit) =
      y.1.appTop f :=
    congrArg y.1.appTop (AffineSpace.homOfVector_appTop_coord _ _ _)
  refine (WeilSheaf.traceFunction_upperStar _ _ n y).trans
    ((WeilSheaf.traceFunction_artinSchreier ψ 1 hn _).trans ?_)
  rw [map_one, one_mul, Scheme.Hom.mapFieldPoints_coe, h]

section LineBundle

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X)
  (s : Y ⟶ affineLine k₀)

omit [Finite k₀] in
/-- The rational points of a trivial line bundle `Y ≅ X ×_{k₀} 𝔸¹` with fibre coordinate `s`
over a rational point `x` of `X` are the pairs `(x, c)`: there is one with coordinate `c`. -/
theorem exists_mapFieldPoints_eq_of_isPullback [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    (K : Type u) [Field K] [Algebra k₀ K] (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K)
    (c : K) :
    ∃ y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints K, π.mapFieldPoints K y = x ∧
      (Scheme.ΓSpecIso (.of K)).hom.hom
        (y.1.appTop (s.appTop (AffineSpace.coord _ PUnit.unit))) = c := by
  let z := (AffineSpace.fieldPointsEquiv k₀ K).symm c
  have hz : x.1 ≫ X ↘ Spec (CommRingCat.of k₀) = z.1 ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀) :=
    x.2.trans z.2.symm
  refine ⟨⟨hπ.lift x.1 z.1 hz, ?_⟩, Subtype.ext (hπ.lift_fst _ _ _), ?_⟩
  · rw [← comp_over π (Spec (CommRingCat.of k₀)), hπ.lift_fst_assoc, x.2]
  · have h : (hπ.lift x.1 z.1 hz).appTop (s.appTop (AffineSpace.coord _ PUnit.unit)) =
        z.1.appTop (AffineSpace.coord _ PUnit.unit) :=
      congrArg (fun φ : Spec (.of K) ⟶ affineLine k₀ ↦ φ.appTop (AffineSpace.coord _ PUnit.unit))
        (hπ.lift_snd _ _ _)
    rw [h, ← AffineSpace.fieldPointsEquiv_apply, Equiv.apply_symm_apply]

omit [Finite k₀] [Y.Over (Spec (CommRingCat.of k₀))] in
/-- The *shear* `(s₁, s₂) ↦ (s₁ + g(s₂), s₂)` of the fibre product `Y ×_X Y` of a trivial line
bundle `Y ≅ X ×_{k₀} 𝔸¹` with fibre coordinate `s` with itself, for a function `g` on `Y`: an
automorphism over the second factor and over `X`, adding `g` pulled back from the second factor
to the fibre coordinate of the first factor. -/
theorem exists_isIso_shear_of_isPullback
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀))) (g : Γ(Y, ⊤)) :
    ∃ τ : pullback π π ⟶ pullback π π, IsIso τ ∧ τ ≫ pullback.snd π π = pullback.snd π π ∧
      τ ≫ pullback.fst π π ≫ π = pullback.fst π π ≫ π ∧
      (τ ≫ pullback.fst π π).appTop (s.appTop (AffineSpace.coord _ PUnit.unit)) =
        (pullback.fst π π).appTop (s.appTop (AffineSpace.coord _ PUnit.unit)) +
          (pullback.snd π π).appTop g := by
  set sf := s.appTop (AffineSpace.coord _ PUnit.unit)
  -- an endomorphism of `Y ×_X Y` is determined by its second component, the image of its first
  -- component in `X` and the fibre coordinate of its first component
  have ext (φ φ' : pullback π π ⟶ pullback π π)
      (h₂ : φ ≫ pullback.snd π π = φ' ≫ pullback.snd π π)
      (h₁ : φ ≫ pullback.fst π π ≫ π = φ' ≫ pullback.fst π π ≫ π)
      (hs : (φ ≫ pullback.fst π π).appTop sf = (φ' ≫ pullback.fst π π).appTop sf) :
      φ = φ' := by
    refine pullback.hom_ext (hπ.hom_ext (by simpa using h₁)
      (AffineSpace.hom_ext ?_ fun ⟨⟩ ↦ hs)) h₂
    simp only [Category.assoc, ← hπ.w]
    rw [reassoc_of% h₁]
  have mk (g : Γ(Y, ⊤)) : ∃ τ : pullback π π ⟶ pullback π π,
      τ ≫ pullback.snd π π = pullback.snd π π ∧
      τ ≫ pullback.fst π π ≫ π = pullback.fst π π ≫ π ∧
      (τ ≫ pullback.fst π π).appTop sf =
        (pullback.fst π π).appTop sf + (pullback.snd π π).appTop g := by
    let v := AffineSpace.homOfVector (pullback.fst π π ≫ π ≫ X ↘ Spec (CommRingCat.of k₀))
      (fun _ : PUnit ↦ (pullback.fst π π).appTop sf + (pullback.snd π π).appTop g)
    have hv : (pullback.fst π π ≫ π) ≫ X ↘ Spec (CommRingCat.of k₀) =
        v ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀) := by
      rw [AffineSpace.homOfVector_over, Category.assoc]
    have h0 : hπ.lift (pullback.fst π π ≫ π) v hv ≫ π = pullback.snd π π ≫ π :=
      (hπ.lift_fst _ _ _).trans pullback.condition
    refine ⟨pullback.lift _ _ h0, pullback.lift_snd _ _ _, ?_, ?_⟩
    · rw [pullback.lift_fst_assoc, hπ.lift_fst]
    · rw [pullback.lift_fst]
      exact (congrArg (fun φ : pullback π π ⟶ affineLine k₀ ↦
        φ.appTop (AffineSpace.coord _ PUnit.unit)) (hπ.lift_snd _ v hv)).trans
          (AffineSpace.homOfVector_appTop_coord _ _ _)
  obtain ⟨τ, h₂, h₁, hs⟩ := mk g
  obtain ⟨τ', h₂', h₁', hs'⟩ := mk (-g)
  have hcomp (φ φ' : pullback π π ⟶ pullback π π) (c c' : Γ(Y, ⊤))
      (h₂ : φ ≫ pullback.snd π π = pullback.snd π π)
      (h₁ : φ ≫ pullback.fst π π ≫ π = pullback.fst π π ≫ π)
      (hs : (φ ≫ pullback.fst π π).appTop sf =
        (pullback.fst π π).appTop sf + (pullback.snd π π).appTop c)
      (h₂' : φ' ≫ pullback.snd π π = pullback.snd π π)
      (h₁' : φ' ≫ pullback.fst π π ≫ π = pullback.fst π π ≫ π)
      (hs' : (φ' ≫ pullback.fst π π).appTop sf =
        (pullback.fst π π).appTop sf + (pullback.snd π π).appTop c') (hc : c + c' = 0) :
      φ ≫ φ' = 𝟙 _ := by
    refine ext _ _ ?_ ?_ ?_
    · rw [Category.assoc, h₂', h₂, Category.id_comp]
    · rw [Category.assoc, h₁', h₁, Category.id_comp]
    · have e : ((φ ≫ φ') ≫ pullback.fst π π).appTop sf =
          φ.appTop ((φ' ≫ pullback.fst π π).appTop sf) := rfl
      have e₂ : φ.appTop ((pullback.snd π π).appTop c') = (pullback.snd π π).appTop c' :=
        congrArg (fun ψ : pullback π π ⟶ Y ↦ ψ.appTop c') h₂
      rw [e, hs', map_add, e₂]
      refine (congrArg (· + (pullback.snd π π).appTop c') hs).trans ?_
      rw [Category.id_comp, add_assoc, ← map_add, hc, map_zero, add_zero]
  exact ⟨τ, ⟨⟨τ', hcomp τ τ' g (-g) h₂ h₁ hs h₂' h₁' hs' (add_neg_cancel g),
    hcomp τ' τ (-g) g h₂' h₁' hs' h₂ h₁ hs (neg_add_cancel g)⟩⟩, h₂, h₁, hs⟩

/-- **Translation invariance.** For the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` with
fibre coordinate `s`, a unit `a` on `X` and a Weil complex `P` on `X`, the pullback of
`M = Rπ₀!(ℒ_ψ(a s) ⊗ π^* P)` to `Y` is invariant under tensoring with `ℒ_ψ(s)`:
`π^* M ≅ ℒ_ψ(s) ⊗ π^* M`. Over `Y`, the shear `(s₁, s₂) ↦ (s₁ + a⁻¹ s₂, s₂)` of `Y ×_X Y`
turns `ℒ_ψ(a s₁)` into `ℒ_ψ(a s₁ + s₂) ≅ ℒ_ψ(s₂) ⊗ ℒ_ψ(a s₁)`; compact-support base change
and the projection formula conclude. -/
theorem WeilComplex.nonempty_iso_upperStar_derivedLowerShriek_tensorLisse_artinSchreierOf
    (ψ : AddChar k₀ (PadicAlgCl l)) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (a : Γ(X, ⊤)) (ha : IsUnit a) (P : WeilComplex k₀ l X) :
    Nonempty ((WeilComplex.upperStar π).obj ((WeilComplex.derivedLowerShriek k₀ l π).obj
        ((WeilComplex.tensorLisse
            (artinSchreierOf ψ (π.appTop a * s.appTop (AffineSpace.coord _ PUnit.unit)))
            (isLisse_artinSchreierOf ψ _)).obj
          ((WeilComplex.upperStar π).obj P))) ≅
      (WeilComplex.tensorLisse (artinSchreierOf ψ (s.appTop (AffineSpace.coord _ PUnit.unit)))
          (isLisse_artinSchreierOf ψ _)).obj
        ((WeilComplex.upperStar π).obj ((WeilComplex.derivedLowerShriek k₀ l π).obj
          ((WeilComplex.tensorLisse
              (artinSchreierOf ψ (π.appTop a * s.appTop (AffineSpace.coord _ PUnit.unit)))
              (isLisse_artinSchreierOf ψ _)).obj
            ((WeilComplex.upperStar π).obj P))))) := by
  obtain ⟨b, hab⟩ := ha.exists_right_inv
  -- the shear `τ : (s₁, s₂) ↦ (s₁ + b s₂, s₂)`, `b = a⁻¹`
  obtain ⟨τ, hτ, hτ₂, hτπ, hτs⟩ := exists_isIso_shear_of_isPullback π s hπ
    (π.appTop b * s.appTop (AffineSpace.coord _ PUnit.unit))
  set sf := s.appTop (AffineSpace.coord _ PUnit.unit)
  set A := π.appTop a * sf with hA
  set q₁ := pullback.fst π π
  set q₂ := pullback.snd π π
  let : (pullback π π).Over (Spec (CommRingCat.of k₀)) :=
    ⟨q₂ ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : q₂.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q₁.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨by
      rw [← comp_over π (Spec (CommRingCat.of k₀)), pullback.condition_assoc, comp_over π]
      rfl⟩
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsSeparated q₂ := MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType q₂ := MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact q₂ := MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (pullback π π ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (q₂ ≫ Y ↘ Spec (CommRingCat.of k₀)))
  have : τ.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨(Category.assoc _ _ _).symm.trans (congrArg (· ≫ Y ↘ Spec (CommRingCat.of k₀)) hτ₂)⟩
  -- the fibre coordinate of `τ ≫ q₁` against `a`: `a (s₁ + b s₂) = s₂ + a s₁`
  have hφA : (τ ≫ q₁).appTop A = q₂.appTop sf + q₁.appTop A := by
    have e₁ : (τ ≫ q₁).appTop (π.appTop a) = q₁.appTop (π.appTop a) :=
      congrArg (fun φ : pullback π π ⟶ X ↦ φ.appTop a) hτπ
    have e₂ : q₂.appTop (π.appTop b) = q₁.appTop (π.appTop b) :=
      congrArg (fun φ : pullback π π ⟶ X ↦ φ.appTop b) pullback.condition.symm
    have e₃ : q₁.appTop (π.appTop a) * q₁.appTop (π.appTop b) = 1 := by
      rw [← map_mul, ← map_mul, hab, map_one, map_one]
    rw [hA]
    simp only [map_mul]
    rw [e₁, hτs, map_mul, e₂]
    linear_combination q₂.appTop sf * e₃
  set L := artinSchreierOf (X := pullback π π) ψ
  obtain ⟨BC₁⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    π π q₂ q₁
    (IsPullback.of_hasPullback π π)
  have hsq : IsPullback τ q₂ q₂ (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by rw [hτ₂, Category.comp_id]⟩
  obtain ⟨BC₂⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    q₂ (𝟙 Y) q₂ τ
    hsq
  obtain ⟨eid⟩ := WeilComplex.nonempty_iso_upperStar_id (k₀ := k₀) (l := l) (X := Y)
  obtain ⟨PF⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse (l := l) q₂
    (artinSchreierOf ψ sf) (isLisse_artinSchreierOf ψ sf)
  obtain ⟨c₁⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) τ q₁
  obtain ⟨t₁⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar (τ ≫ q₁)
    (artinSchreierOf ψ A) (isLisse_artinSchreierOf ψ A)
  obtain ⟨a₁⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) (τ ≫ q₁) ψ A
  obtain ⟨m₁⟩ := nonempty_iso_tensorObj_artinSchreierOf (k₀ := k₀) (l := l) ψ (q₂.appTop sf)
    (q₁.appTop A)
  obtain ⟨i₁⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (a₁ ≪≫ eqToIso (congrArg L hφA) ≪≫ m₁.symm) (ProEtale.IsAdicLisseSheaf.upperStar _
      (isLisse_artinSchreierOf ψ A))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ _).dual
      (isLisse_artinSchreierOf ψ (q₁.appTop A)))
  obtain ⟨c₂⟩ := WeilComplex.nonempty_iso_tensorLisse_comp (L (q₂.appTop sf)) (L (q₁.appTop A))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨c₃⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) (τ ≫ q₁) π
  obtain ⟨c₄⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) q₁ π
  obtain ⟨e₅⟩ := WeilComplex.nonempty_upperStar_iso_of_eq (k₀ := k₀) (l := l)
    ((Category.assoc _ _ _).trans hτπ)
  obtain ⟨t₂⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar q₁
    (artinSchreierOf ψ A) (isLisse_artinSchreierOf ψ A)
  obtain ⟨a₂⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) q₁ ψ A
  obtain ⟨i₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso a₂
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ A))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨a₃⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) q₂ ψ sf
  obtain ⟨i₃⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso a₃
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ sf))
    (isLisse_artinSchreierOf ψ _)
  set K := (WeilComplex.tensorLisse (artinSchreierOf ψ A) (isLisse_artinSchreierOf ψ _)).obj
    ((WeilComplex.upperStar π).obj P)
  -- `φ^* π^* P ≅ q₁^* π^* P` for `φ = τ ≫ q₁`
  let pP : (WeilComplex.upperStar (τ ≫ q₁)).obj ((WeilComplex.upperStar π).obj P) ≅
      (WeilComplex.upperStar q₁).obj ((WeilComplex.upperStar π).obj P) :=
    (c₃.app P).symm ≪≫ e₅.app P ≪≫ c₄.app P
  -- `q₁^* K ≅ ℒ_ψ(a s₁) ⊗ q₁^* π^* P`
  let eK : (WeilComplex.upperStar q₁).obj K ≅
      (WeilComplex.tensorLisse (L (q₁.appTop A)) (isLisse_artinSchreierOf ψ _)).obj
        ((WeilComplex.upperStar q₁).obj ((WeilComplex.upperStar π).obj P)) :=
    t₂.app _ ≪≫ i₂.app _
  -- `τ^* q₁^* K ≅ q₂^* ℒ_ψ(s) ⊗ q₁^* K`
  let E₁ : (WeilComplex.upperStar τ).obj ((WeilComplex.upperStar q₁).obj K) ≅
      (WeilComplex.tensorLisse ((WeilSheaf.upperStar q₂).obj (artinSchreierOf ψ sf))
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ sf))).obj
        ((WeilComplex.upperStar q₁).obj K) :=
    (c₁.app K).symm ≪≫ t₁.app _ ≪≫ i₁.app _ ≪≫ (c₂.app _).symm ≪≫
      (WeilComplex.tensorLisse (L (q₂.appTop sf)) (isLisse_artinSchreierOf ψ _)).mapIso
        ((WeilComplex.tensorLisse (L (q₁.appTop A)) (isLisse_artinSchreierOf ψ _)).mapIso pP ≪≫
          eK.symm) ≪≫ (i₃.app _).symm
  exact ⟨BC₁.app K ≪≫ (eid.app _).symm ≪≫ BC₂.app _ ≪≫
    (WeilComplex.derivedLowerShriek k₀ l q₂).mapIso E₁ ≪≫ (PF.app _).symm ≪≫
    (WeilComplex.tensorLisse (artinSchreierOf ψ sf) (isLisse_artinSchreierOf ψ sf)).mapIso
      (BC₁.app K).symm⟩

end LineBundle

/-- **Relative vanishing** (blueprint `lemma-integral-linear-character--2`, in the relative
form used in the proofs of `lemma-fourier-transform-constant-sheaf` and
`proposition-fourier-inversion`). Let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle with
fibre coordinate `s`, let `a` be a unit on `X` and `ψ` nontrivial. Then `Rπ₀!(ℒ_ψ(a s) ⊗ π^* P) = 0`
for every Weil complex `P` on `X`: on the fibre over a geometric point `x̄` this is
`P_x̄ ⊗ RΓ_c(𝔸¹_x̄, ℒ_ψ(a(x̄) s)) = 0`, `a(x̄) ≠ 0`. -/
theorem WeilComplex.isZero_derivedLowerShriek_tensorLisse_artinSchreierOf_upperStar
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (a : Γ(X, ⊤)) (ha : IsUnit a) (P : WeilComplex k₀ l X) :
    IsZero ((WeilComplex.derivedLowerShriek k₀ l π).obj
      ((WeilComplex.tensorLisse
          (artinSchreierOf ψ (π.appTop a * s.appTop (AffineSpace.coord _ PUnit.unit)))
          (isLisse_artinSchreierOf ψ _)).obj
        ((WeilComplex.upperStar π).obj P))) := by
  set M := (WeilComplex.derivedLowerShriek k₀ l π).obj
    ((WeilComplex.tensorLisse
        (artinSchreierOf ψ (π.appTop a * s.appTop (AffineSpace.coord _ PUnit.unit)))
        (isLisse_artinSchreierOf ψ _)).obj
      ((WeilComplex.upperStar π).obj P))
  obtain ⟨E⟩ := WeilComplex.nonempty_iso_upperStar_derivedLowerShriek_tensorLisse_artinSchreierOf
    π s ψ hπ a ha P
  obtain ⟨d, hd⟩ := AddChar.ne_one_iff.1 hψ
  refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
    (_root_.DerivedCategory.isZero_of_forall_isZero_homology _ fun j ↦
      (isZero_homologySheaf_obj_iff j M).1 ?_)
  refine WeilSheaf.isZero_of_traceFunction_eq_zero _ fun n hn x ↦ ?_
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  obtain ⟨c, hc⟩ := Algebra.trace_surjective k₀ (FiniteField.galoisExtension k₀ n) d
  obtain ⟨y, hyx, hyc⟩ := exists_mapFieldPoints_eq_of_isPullback π s hπ _ x c
  have h := WeilSheaf.traceFunction_congr ((homologySheaf j).mapIso E) n y
  rw [WeilSheaf.traceFunction_congr (WeilComplex.homologySheafTensorLisseIso _ _ _ j),
    WeilSheaf.traceFunction_ihom_dual,
    WeilSheaf.traceFunction_congr (WeilComplex.homologySheafUpperStarIso π j M),
    WeilSheaf.traceFunction_upperStar, hyx, WeilSheaf.traceFunction_artinSchreierOf ψ _ hn,
    hyc, hc] at h
  have h' : (1 - ψ d) * ((homologySheaf j).obj M).traceFunction n x = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 (Ne.symm hd))

end AlgebraicGeometry
