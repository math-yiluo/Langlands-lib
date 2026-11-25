/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.LocalTerm

/-!

# Local terms along a point of the fixed locus

Let `c` be an endocorrespondence of `(X, K)` with fixed locus `F` and `y` a rational point of `C`
lying on the fixed locus, so that `y` lifts to a point `F.liftPoint y hy` of the fixed locus. For
an open and closed subscheme `B` of the fixed locus, proper over `s`, with underlying set `{y}`,
the local term along `B` is the integral of a Borel–Moore section `γ` of the point as soon as the
restriction of the trace class to `B` is the pushforward of `γ` along the point of `B`
(`Correspondence.localTerm_traceClass_eq_integral_of_restrict_eq`). This is the formal last step
of the computation of local terms at an isolated fixed point, both on the curve route (blueprint
`corollary-contracting-local-terms-point`, item 3) and for contracting correspondences. The trace
class of a correspondence vanishes when the pulled back coefficient does
(`Correspondence.traceClass_eq_zero_of_isZero`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

variable {c : Correspondence ℓ K}

/-- A `k`-point of the support lying on the fixed locus, as a point of the fixed locus. -/
noncomputable def FixedLocus.liftPoint (F : c.FixedLocus) (y : RationalPoint c.C)
    (hy : y ≫ c.c₁ = y ≫ c.c₂) : RationalPoint F.F :=
  F.isLimit.lift (Fork.ofι (P := point k) y hy)

@[reassoc (attr := simp)]
lemma FixedLocus.liftPoint_ι (F : c.FixedLocus) (y : RationalPoint c.C)
    (hy : y ≫ c.c₁ = y ≫ c.c₂) : F.liftPoint y hy ≫ F.ι = y :=
  Fork.IsLimit.lift_ι F.isLimit

lemma FixedLocus.liftPoint_withCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K')
    (y : RationalPoint c.C) (hy : y ≫ c.c₁ = y ≫ c.c₂) :
    (F.withCoeff K' u').liftPoint y hy = F.liftPoint y hy :=
  rfl

variable (c) in
/-- The trace class of a correspondence whose pulled back coefficient `Lc₂^* K` vanishes is
zero: the mate of `u` is a map out of the zero object. -/
lemma traceClass_eq_zero_of_isZero (F : c.FixedLocus)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K)) :
    c.traceClass F = 0 := by
  have hm : c.mate = 0 := by
    rw [mate, ← MonoidalClosed.curry'_uncurry' (0 : 𝟙_ _ ⟶ _)]
    exact congrArg _ (hK.eq_of_src _ _)
  rw [traceClass, hm, zero_comp, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp,
    comp_zero]

/-- The local term along an open and closed subscheme `B` of the fixed locus with underlying set
`{y}` is the integral of a Borel–Moore section `γ` of the point if the restriction of the trace
class to `B` is the pushforward of `γ` along the point of `B`. -/
lemma localTerm_traceClass_eq_integral_of_restrict_eq {c : Correspondence ℓ K}
    (F : c.FixedLocus) {y : RationalPoint c.C} (hy : y ≫ c.c₁ = y ≫ c.c₂)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base = {(F.liftPoint y hy).left.base (default : Spec (.of k))})
    (γ : BorelMooreSection ℓ (point k))
    (H : ∀ (e : point k ⟶ B) [IsProper e.left], e ≫ j = F.liftPoint y hy →
      (c.traceClass F).restrict j = BorelMooreSection.pushforward e γ) :
    (c.traceClass F).localTerm j = γ.integral := by
  have hrange : Set.range (F.liftPoint y hy).left.base ⊆ Set.range j.left.base := by
    rw [hB]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of k)) z default]
    rfl
  let e : point k ⟶ B := Over.homMk (IsOpenImmersion.lift j.left _ hrange) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (F.liftPoint y hy))
  have he : e ≫ j = F.liftPoint y hy :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have : IsProper (e.left ≫ B.hom) := by
    rw [Over.w e]
    exact inferInstanceAs (IsProper (𝟙 (Spec (.of k))))
  have : IsProper e.left := IsProper.of_comp e.left B.hom
  rw [BorelMooreSection.localTerm, H e he]
  exact BorelMooreSection.integral_pushforward e _

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
