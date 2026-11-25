/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Correspondence

/-!

# Products over the base point and the fixed square of a correspondence

For separated `k`-schemes of finite type `X, Y`, objects of `Over (Spec (.of k))`, the product
`X ⨯ Y` in `Over (Spec (.of k))` is the fibre product `X ×_s Y` over the base point
(`ProEtale.CondensedRing.isPullback_prod_left`); it is again separated of finite type over `s`.

An endocorrespondence `c = (C, c₁, c₂, u)` of `(X, K)` has the *support map*
`c = (c₁, c₂) : C ⟶ X ⨯ X` (`ProEtale.CondensedRing.Correspondence.support`), with the exceptional
leg `c₁ = c ≫ p₁` and the ordinary leg `c₂ = c ≫ p₂`. Its fixed locus `ι : Fix(c) ⟶ C`, the
equalizer of `c₁` and `c₂`, fits in the *fixed square*
```
Fix(c) ──ι──▶ C
   │d         │c
   ▼          ▼
   X ───Δ──▶ X ⨯ X
```
with `d = ι ≫ c₁ = ι ≫ c₂`, which is cartesian
(`ProEtale.CondensedRing.Correspondence.FixedLocus.isPullback`, blueprint
`definition-correspondence--3`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Products over the base point -/

section Product

variable {k : Type u} [Field k]

/-- The product `X ⨯ Y` in `Over (Spec (.of k))` is the fibre product of the structure
morphisms. -/
lemma isPullback_prod_left (X Y : Over (Spec (.of k))) :
    IsPullback (prod.fst : X ⨯ Y ⟶ X).left (prod.snd : X ⨯ Y ⟶ Y).left X.hom Y.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd) (prodIsProd X Y)

/-- The product `X ⨯ Y` is the fibre product of the structure morphisms over the base point:
the square `p_Y ≫ a_Y = p_X ≫ a_X` is cartesian. -/
lemma isPullback_prod_toPoint (X Y : Over (Spec (.of k))) :
    IsPullback (prod.snd : X ⨯ Y ⟶ Y) prod.fst (toPoint Y) (toPoint X) := by
  have h : IsPullback (prod.snd : X ⨯ Y ⟶ Y) prod.fst ((isTerminalPoint k).from Y)
      ((isTerminalPoint k).from X) :=
    (IsPullback.of_is_product (prodIsProd X Y) (isTerminalPoint k)).flip
  rwa [toPoint_ext ((isTerminalPoint k).from Y) (toPoint Y),
    toPoint_ext ((isTerminalPoint k).from X) (toPoint X)] at h

variable {X Y : Over (Spec (.of k))}

instance [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (prod.fst : X ⨯ Y ⟶ X).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y).flip inferInstance

instance [QuasiCompact Y.hom] : QuasiCompact (prod.fst : X ⨯ Y ⟶ X).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y).flip inferInstance

instance [IsSeparated Y.hom] : IsSeparated (prod.fst : X ⨯ Y ⟶ X).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y).flip inferInstance

instance [IsProper Y.hom] : IsProper (prod.fst : X ⨯ Y ⟶ X).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y).flip inferInstance

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (prod.snd : X ⨯ Y ⟶ Y).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y) inferInstance

instance [QuasiCompact X.hom] : QuasiCompact (prod.snd : X ⨯ Y ⟶ Y).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y) inferInstance

instance [IsSeparated X.hom] : IsSeparated (prod.snd : X ⨯ Y ⟶ Y).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y) inferInstance

instance [IsProper X.hom] : IsProper (prod.snd : X ⨯ Y ⟶ Y).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left X Y) inferInstance

lemma prod_hom_eq (X Y : Over (Spec (.of k))) :
    (X ⨯ Y).hom = (prod.fst : X ⨯ Y ⟶ X).left ≫ X.hom :=
  (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm

instance [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⨯ Y).hom := by
  rw [prod_hom_eq]
  infer_instance

instance [QuasiCompact X.hom] [QuasiCompact Y.hom] : QuasiCompact (X ⨯ Y).hom := by
  rw [prod_hom_eq]
  infer_instance

instance [IsSeparated X.hom] [IsSeparated Y.hom] : IsSeparated (X ⨯ Y).hom := by
  rw [prod_hom_eq]
  infer_instance

instance [IsProper X.hom] [IsProper Y.hom] : IsProper (X ⨯ Y).hom := by
  rw [prod_hom_eq]
  infer_instance

/-- The diagonal `Δ_X : X ⟶ X ⨯ X` of a separated scheme is a closed immersion. -/
instance [IsSeparated X.hom] : IsClosedImmersion (diag X).left := by
  have h := isPullback_prod_left X X
  have e : (diag X).left = pullback.diagonal X.hom ≫ h.isoPullback.inv := by
    rw [Iso.eq_comp_inv]
    apply pullback.hom_ext
    · simp [← Over.comp_left]
    · simp [← Over.comp_left]
  rw [e]
  infer_instance

end Product

/-! ### The support map and the fixed square -/

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

/-- The *support map* `c = (c₁, c₂) : C ⟶ X ⨯ X` of an endocorrespondence (blueprint
`definition-correspondence`): its first component is the exceptional leg `c₁`, its second the
ordinary leg `c₂`. -/
noncomputable def support : c.C ⟶ X ⨯ X :=
  prod.lift c.c₁ c.c₂

@[reassoc (attr := simp)]
lemma support_fst : c.support ≫ prod.fst = c.c₁ :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
lemma support_snd : c.support ≫ prod.snd = c.c₂ :=
  prod.lift_snd _ _

namespace FixedLocus

variable {c} (F : c.FixedLocus)

/-- The map `d = ι ≫ c₁ : Fix(c) ⟶ X` of the fixed square. -/
noncomputable def d : F.F ⟶ X :=
  F.ι ≫ c.c₁

lemma ι_c₁ : F.ι ≫ c.c₁ = F.d :=
  rfl

lemma ι_c₂ : F.ι ≫ c.c₂ = F.d :=
  F.w.symm

lemma ι_support : F.ι ≫ c.support = F.d ≫ diag X := by
  apply prod.hom_ext <;> simp [ι_c₁, ι_c₂]

/-- **The fixed square is cartesian** (blueprint `definition-correspondence--3`): the fixed
locus `Fix(c)` is the fibre product `C ×_{X ⨯ X} X` of the support map `c : C ⟶ X ⨯ X` and the
diagonal `Δ_X`, with projections `ι : Fix(c) ⟶ C` and `d : Fix(c) ⟶ X`. -/
theorem isPullback : IsPullback F.ι F.d c.support (diag X) := by
  refine ⟨⟨F.ι_support⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) ?_⟩⟩
  · refine F.isLimit.lift (Fork.ofι s.fst ?_)
    have h₁ := s.condition =≫ prod.fst
    have h₂ := s.condition =≫ prod.snd
    simp only [Category.assoc, support_fst, support_snd, diag, prod.lift_fst,
      prod.lift_snd] at h₁ h₂
    exact h₁.trans h₂.symm
  · exact F.isLimit.fac _ WalkingParallelPair.zero
  · have h₁ := s.condition =≫ prod.fst
    simp only [Category.assoc, support_fst, diag, prod.lift_fst, Category.comp_id] at h₁
    rw [d, ← Category.assoc]
    erw [F.isLimit.fac _ WalkingParallelPair.zero]
    exact h₁
  · intro s m h₁ _
    exact Fork.IsLimit.hom_ext F.isLimit
      (h₁.trans (F.isLimit.fac (Fork.ofι s.fst _) WalkingParallelPair.zero).symm)

/-- The inclusion of the fixed locus is a closed immersion: it is the base change of the
diagonal. -/
instance isClosedImmersion_ι : IsClosedImmersion F.ι.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (F.isPullback.map (Over.forget _)).flip (inferInstanceAs (IsClosedImmersion (diag X).left))

/-- The exceptional composition isomorphism of the fixed square (blueprint
`definition-correspondence--3`): `Rd^! ≅ Rc₁^! ⋙ Rι^!`, from `d = ι ≫ c₁`, the only
unconditional `!`-transport of the two legs in the fixed square. -/
noncomputable def upperShriekDIso :
    boundedConstructibleUpperShriek ℓ F.d ≅
      boundedConstructibleUpperShriek ℓ c.c₁ ⋙
        boundedConstructibleUpperShriek ℓ F.ι :=
  boundedConstructibleUpperShriekComp_padicAlgCl ℓ F.ι c.c₁

end FixedLocus

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
