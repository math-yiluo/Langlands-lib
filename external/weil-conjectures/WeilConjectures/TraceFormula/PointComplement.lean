/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurvePieces

/-!

# The open complement of a rational point

For a rational point `x : s ⟶ X` of a separated `k`-scheme of finite type, the open complement
`j : X ∖ {x} ⟶ X` (`ProEtale.CondensedRing.pointComplι`) is a separated `k`-scheme of finite type,
complementary to `x`. If `x` is fixed by an endomorphism `g` of `X` injective on points, the
square `g_U ≫ j = j ≫ g` is cartesian (`ProEtale.CondensedRing.exists_isPullback_pointComplι`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

section PointCompl

/-- The open complement `X ∖ {x}` of a rational point `x`, an open subset of `X`. -/
noncomputable def pointComplOpens (x : RationalPoint X) : X.left.Opens :=
  ⟨(Set.range x.left.base)ᶜ, x.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open complement `U = X ∖ {x}` of a rational point `x`, as a scheme over `s`. -/
noncomputable abbrev pointCompl (x : RationalPoint X) : Over (Spec (.of k)) :=
  Over.mk ((pointComplOpens x).ι ≫ X.hom)

/-- The open immersion `j : X ∖ {x} ⟶ X` of the complement of a rational point. -/
noncomputable abbrev pointComplι (x : RationalPoint X) : pointCompl x ⟶ X :=
  Over.homMk (pointComplOpens x).ι

instance (x : RationalPoint X) : IsOpenImmersion (pointComplι x).left :=
  inferInstanceAs (IsOpenImmersion (pointComplOpens x).ι)

instance (x : RationalPoint X) : LocallyOfFiniteType (pointCompl x).hom :=
  inferInstanceAs (LocallyOfFiniteType ((pointComplOpens x).ι ≫ X.hom))

instance (x : RationalPoint X) : IsSeparated (pointCompl x).hom :=
  inferInstanceAs (IsSeparated ((pointComplOpens x).ι ≫ X.hom))

instance (x : RationalPoint X) : QuasiCompact (pointCompl x).hom := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiCompact (pointComplOpens x).ι := inferInstance
  exact inferInstanceAs (QuasiCompact ((pointComplOpens x).ι ≫ X.hom))

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma range_pointComplι (x : RationalPoint X) :
    Set.range (pointComplι x).left.base = (Set.range x.left.base)ᶜ :=
  Scheme.Opens.range_ι _

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The open complement of a rational point and the point are complementary. -/
lemma isCompl_range_pointComplι (x : RationalPoint X) :
    IsCompl (Set.range (pointComplι x).left.base) (Set.range x.left.base) := by
  rw [range_pointComplι]
  exact isCompl_compl.symm

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The open complement of a rational point `x` fixed by an endomorphism `g` of `X`, injective on
points, is stable under `g`, and the square `g_U ≫ j = j ≫ g` is cartesian. -/
lemma exists_isPullback_pointComplι (x : RationalPoint X) (g : X ⟶ X)
    (hg : Function.Injective g.left.base) (hx : x ≫ g = x) :
    ∃ gU : pointCompl x ⟶ pointCompl x, IsPullback gU (pointComplι x) (pointComplι x) g := by
  set x₀ := x.left.base (default : Spec (.of k)) with hx₀
  have hxg : g.left.base x₀ = x₀ := by
    rw [hx₀, ← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
  have hpt (y : X.left) : y ∈ Set.range x.left.base ↔ y = x₀ := by
    refine ⟨?_, fun h ↦ ⟨(default : Spec (.of k)), h.symm⟩⟩
    rintro ⟨z, rfl⟩
    rw [hx₀, Subsingleton.elim (α := Spec (.of k)) z default]
  have hrange : Set.range ((pointComplι x).left ≫ g.left).base ⊆
      Set.range (pointComplι x).left.base := by
    rintro _ ⟨y, rfl⟩
    have hy : (pointComplι x).left.base y ∈ Set.range (pointComplι x).left.base := ⟨y, rfl⟩
    rw [range_pointComplι, Set.mem_compl_iff, hpt] at hy ⊢
    rw [Scheme.Hom.comp_apply, ← hxg]
    exact fun h ↦ hy (hg h)
  have hι : (pointCompl x).hom = (pointComplι x).left ≫ X.hom := rfl
  refine ⟨Over.homMk (IsOpenImmersion.lift (pointComplι x).left _ hrange) ?_, ?_⟩
  · rw [hι, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Over.w g]
  · refine IsOpenImmersion.isPullback_over_of_preimage_range_subset _
      (Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)) ?_
    intro y hy
    rw [range_pointComplι, Set.mem_preimage, Set.mem_compl_iff, hpt] at hy
    rw [range_pointComplι, Set.mem_compl_iff, hpt]
    rintro rfl
    exact hy hxg

end PointCompl

/-! ### Preimages of the complement of a point -/

section Preimage

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The preimage `g⁻¹(X ∖ {x})` of the open complement of a rational point under `g : Y ⟶ X`,
as a scheme over `s`. -/
noncomputable abbrev preimagePointCompl (g : Y ⟶ X) (x : RationalPoint X) :
    Over (Spec (.of k)) :=
  Over.mk ((g.left ⁻¹ᵁ pointComplOpens x).ι ≫ Y.hom)

instance (g : Y ⟶ X) (x : RationalPoint X) : LocallyOfFiniteType (preimagePointCompl g x).hom :=
  inferInstanceAs (LocallyOfFiniteType ((g.left ⁻¹ᵁ pointComplOpens x).ι ≫ Y.hom))

instance (g : Y ⟶ X) (x : RationalPoint X) : IsSeparated (preimagePointCompl g x).hom :=
  inferInstanceAs (IsSeparated ((g.left ⁻¹ᵁ pointComplOpens x).ι ≫ Y.hom))

instance (g : Y ⟶ X) (x : RationalPoint X) : QuasiCompact (preimagePointCompl g x).hom := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have : QuasiCompact (g.left ⁻¹ᵁ pointComplOpens x).ι := inferInstance
  exact inferInstanceAs (QuasiCompact ((g.left ⁻¹ᵁ pointComplOpens x).ι ≫ Y.hom))

/-- The open immersion `g⁻¹(X ∖ {x}) ⟶ Y`. -/
noncomputable abbrev preimagePointComplι (g : Y ⟶ X) (x : RationalPoint X) :
    preimagePointCompl g x ⟶ Y :=
  Over.homMk (g.left ⁻¹ᵁ pointComplOpens x).ι

instance (g : Y ⟶ X) (x : RationalPoint X) : IsOpenImmersion (preimagePointComplι g x).left :=
  inferInstanceAs (IsOpenImmersion (g.left ⁻¹ᵁ pointComplOpens x).ι)

/-- The restriction `g⁻¹(X ∖ {x}) ⟶ X ∖ {x}` of `g`. -/
noncomputable def preimagePointComplRestrict (g : Y ⟶ X) (x : RationalPoint X) :
    preimagePointCompl g x ⟶ pointCompl x :=
  Over.homMk (g.left ∣_ pointComplOpens x) (by
    change _ ≫ (pointComplOpens x).ι ≫ X.hom = _
    rw [morphismRestrict_ι_assoc, Over.w g]
    rfl)

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The restriction of `g` to the preimage of the complement of a point is a base change of
`g`. -/
lemma isPullback_preimagePointComplRestrict (g : Y ⟶ X) (x : RationalPoint X) :
    IsPullback (preimagePointComplRestrict g x) (preimagePointComplι g x) (pointComplι x) g := by
  have w : preimagePointComplRestrict g x ≫ pointComplι x = preimagePointComplι g x ≫ g := by
    ext1
    exact morphismRestrict_ι _ _
  exact IsPullback.of_map (Over.forget _) w (isPullback_morphismRestrict g.left (pointComplOpens x))

/-- The inclusion `g⁻¹(X ∖ {x}) ⟶ g'⁻¹(X ∖ {x})` of preimages. -/
noncomputable def preimagePointComplHomOfLE {g g' : Y ⟶ X} {x : RationalPoint X}
    (hle : g.left ⁻¹ᵁ pointComplOpens x ≤ g'.left ⁻¹ᵁ pointComplOpens x) :
    preimagePointCompl g x ⟶ preimagePointCompl g' x :=
  Over.homMk (Y.left.homOfLE hle) (by
    change _ ≫ (g'.left ⁻¹ᵁ pointComplOpens x).ι ≫ Y.hom = _
    rw [Scheme.homOfLE_ι_assoc]
    rfl)

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
@[reassoc (attr := simp)]
lemma preimagePointComplHomOfLE_ι {g g' : Y ⟶ X} {x : RationalPoint X}
    (hle : g.left ⁻¹ᵁ pointComplOpens x ≤ g'.left ⁻¹ᵁ pointComplOpens x) :
    preimagePointComplHomOfLE hle ≫ preimagePointComplι g' x = preimagePointComplι g x := by
  ext1
  exact Scheme.homOfLE_ι _ hle

instance {g g' : Y ⟶ X} {x : RationalPoint X}
    (hle : g.left ⁻¹ᵁ pointComplOpens x ≤ g'.left ⁻¹ᵁ pointComplOpens x) :
    IsOpenImmersion (preimagePointComplHomOfLE hle).left :=
  inferInstanceAs (IsOpenImmersion (Y.left.homOfLE hle))

end Preimage

end AlgebraicGeometry.ProEtale.CondensedRing
