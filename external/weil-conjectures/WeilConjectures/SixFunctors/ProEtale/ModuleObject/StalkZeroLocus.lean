/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The vanishing locus of a constructible `ℚ̲̄_ℓ`-module

For a module object `M` over `ℚ̲̄_ℓ,X` on `X_proét`, `ProEtale.CondensedRing.stalkZeroLocus ℓ M`
is the set of points `x` of `X` such that the pullback of `M` along every geometric point
`Spec Ω ⟶ X` over `x` (`Ω` separably closed) vanishes. This is the pro-étale analogue of
`AlgebraicGeometry.Etale.stalkZeroLocus`.

* If `M` is pro-étale locally finitely presented, the pullback of `M` along a geometric point over
  `x` vanishes exactly when the fibre rank `fiberRankFun ℓ M x` is zero
  (`ProEtale.CondensedRing.isZero_upperStar_iff_fiberRankFun_eq_zero`); in particular vanishing
  at one geometric point over `x` gives vanishing at all of them.
* For `M` constructible, vanishing at one geometric point over `x` gives
  `x ∈ stalkZeroLocus ℓ M` (`ProEtale.CondensedRing.mem_stalkZeroLocus_of_isZero_upperStar`).
* For `M` constructible on a scheme of finite type over a field, `stalkZeroLocus ℓ M` is
  a constructible subset (`ProEtale.CondensedRing.isConstructible_stalkZeroLocus`): on each
  stratum the fibre rank is locally constant
  (`ProEtale.CondensedRing.isLocallyConstant_fiberRankFun`).
* For a bounded constructible complex `K` on such a scheme, the common vanishing locus
  `ProEtale.CondensedRing.complexStalkZeroLocus ℓ K` of its cohomology sheaves is constructible
  (`ProEtale.CondensedRing.isConstructible_complexStalkZeroLocus`), only finitely many of them
  being nonzero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Topology

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (ℓ) in
/-- The *vanishing locus* of a `ℚ̲̄_ℓ,X`-module `M`: the points `x` such that the pullback of `M`
along every geometric point `Spec Ω ⟶ X` over `x` vanishes. -/
def stalkZeroLocus {X : Scheme.{u}} (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) : Set X :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
    s (IsLocalRing.closedPoint Ω) = x →
      IsZero ((s)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)}

/-- The free module of rank `0` is zero. -/
lemma isZero_finiteFree_zero {W : Scheme.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    IsZero (Mod.finiteFree (condensedRingObj Λ W) 0) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext _ _ fun i ↦ i.elim0

/-- Over a nonempty quasi-compact quasi-separated scheme, the free module `(ℚ̲̄_ℓ)^d` vanishes
exactly when `d = 0`: the endomorphisms of the unit evaluate to the nonzero ring `ℚ̄_ℓ`. -/
lemma isZero_finiteFree_iff {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    [Nonempty W] (d : ℕ) :
    IsZero (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) d) ↔
      d = 0 := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨w⟩ := ‹Nonempty W›
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have h1 : (1 : End (Mod.regular
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W))) = 0 := by
      apply End.ext
      rw [End.one_asHom, End.zero_asHom,
        ← biproduct.ι_π_self (fun _ : Fin d ↦ Mod.regular _) i,
        h.eq_of_tgt (biproduct.ι (fun _ : Fin d ↦ Mod.regular _) i) 0, zero_comp]
    have h2 := congrArg (endValueRingHom (ℓ := ℓ) w) h1
    rw [map_one, map_zero] at h2
    exact one_ne_zero h2
  · rintro rfl
    exact isZero_finiteFree_zero _

/-- **Vanishing at a geometric point is read off the fibre rank.** Let `N` be a `ℚ̲̄_ℓ,Y`-module
whose pullbacks to the members of a pro-étale cover are finitely presented. The pullback of `N`
along a geometric point `s : Spec Ω ⟶ Y` vanishes if and only if the fibre rank of `N` at the
image point is zero: `s` lifts to a member of the cover, then to an affine chart where `N` is the
cokernel of a matrix, and factors through the residue field of the chart at its image point, over
which the pullback of `N` is free of rank the fibre rank. -/
theorem isZero_upperStar_iff_fiberRankFun_eq_zero {Y : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (h𝒰 : ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (𝒰.X i))
      ((𝒰.f i)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj N))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    IsZero ((s)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj N) ↔
      fiberRankFun ℓ N (s (IsLocalRing.closedPoint Ω)) = 0 := by
  obtain ⟨i, g, hg⟩ := 𝒰.exists_comp_eq_of_isSepClosed_of_proetale s
  obtain ⟨W, _, i₀, _, w, hw, ⟨n, m, φ, ⟨e⟩⟩⟩ :=
    exists_isOpenImmersion_isFinitelyPresented (𝒰.f i) (h𝒰 i) (g (IsLocalRing.closedPoint Ω))
  have hrange : Set.range g.base ⊆ Set.range i₀.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    exact ⟨w, hw⟩
  let g' := IsOpenImmersion.lift i₀ g hrange
  have hg' : g' ≫ i₀ = g := IsOpenImmersion.lift_fac _ _ _
  let w' := g' (IsLocalRing.closedPoint Ω)
  let c : Spec (.of Ω) ⟶ Spec (W.residueField w') :=
    Spec.map (W.descResidueField (Scheme.stalkClosedPointTo g'))
  have hc : c ≫ W.fromSpecResidueField w' = g' :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω W g'
  obtain ⟨d, hd⟩ := exists_hasFiberRank_cokernel φ w'
  have hd' := hd.of_iso e.symm
  have hdeq := hd'.eq_fiberRankFun (i₀ ≫ 𝒰.f i)
  have hs : c ≫ W.fromSpecResidueField w' ≫ i₀ ≫ 𝒰.f i = s := by
    rw [reassoc_of% hc, reassoc_of% hg', hg]
  have hpt : (i₀ ≫ 𝒰.f i) w' = s (IsLocalRing.closedPoint Ω) := by
    rw [← hs]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  obtain ⟨e'⟩ := hd'
  let E : (s)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj N ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of Ω))) d :=
    (upperStarCongr _ hs.symm).app N ≪≫
      (upperStarComp _ c (W.fromSpecResidueField w' ≫ i₀ ≫ 𝒰.f i)).app N ≪≫
      (c)^*⟦_⟧.mapIso ((upperStarComp _ (W.fromSpecResidueField w') (i₀ ≫ 𝒰.f i)).app N ≪≫ e') ≪≫
      upperStarFiniteFreeIso _ c d
  rw [E.isZero_iff, isZero_finiteFree_iff, ← hpt, ← hdeq]

/-- A geometric point of `X` exists over every point. -/
lemma exists_spec_sepClosure (X : Scheme.{u}) (x : X) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X),
      s (IsLocalRing.closedPoint Ω) = x :=
  ⟨SeparableClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x)
      (SeparableClosure (X.residueField x)))) ≫ X.fromSpecResidueField x, by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _⟩

/-- For a module locally finitely presented over a pro-étale cover, `x` lies in the vanishing
locus iff the fibre rank at `x` is zero. -/
lemma mem_stalkZeroLocus_iff_fiberRankFun_eq_zero {Y : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (h𝒰 : ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (𝒰.X i))
      ((𝒰.f i)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj N)) (y : Y) :
    y ∈ stalkZeroLocus ℓ N ↔ fiberRankFun ℓ N y = 0 := by
  constructor
  · intro h
    obtain ⟨Ω, _, _, s, rfl⟩ := exists_spec_sepClosure Y y
    exact (isZero_upperStar_iff_fiberRankFun_eq_zero 𝒰 h𝒰 s).1 (h Ω s rfl)
  · rintro h Ω _ _ s rfl
    exact (isZero_upperStar_iff_fiberRankFun_eq_zero 𝒰 h𝒰 s).2 h

/-- Points of an immersed subscheme in the vanishing locus, read on the subscheme. -/
lemma mem_stalkZeroLocus_iff_of_isImmersion {X T : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) (j : T ⟶ X) [IsImmersion j]
    (t : T) :
    j t ∈ stalkZeroLocus ℓ M ↔
      t ∈ stalkZeroLocus ℓ ((j)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) := by
  constructor
  · intro h Ω _ _ s hs
    exact (h Ω (s ≫ j) (by rw [Scheme.Hom.comp_apply, hs])).of_iso
      ((upperStarComp _ s j).app M).symm
  · intro h Ω _ _ s hs
    obtain ⟨t', rfl⟩ := IsImmersion.exists_comp_eq_of_field j s ⟨t, hs.symm⟩
    have ht' : t' (IsLocalRing.closedPoint Ω) = t := j.isEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply]; exact hs)
    exact (h Ω t' ht').of_iso ((upperStarComp _ t' j).app M)

/-- **For constructible modules, vanishing at one geometric point suffices**: the pullback to
every other geometric point over the same point then vanishes. -/
theorem mem_stalkZeroLocus_of_isZero_upperStar {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)}
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      M) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (h : IsZero ((s)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) :
    s (IsLocalRing.closedPoint Ω) ∈ stalkZeroLocus ℓ M := by
  obtain ⟨S, hS⟩ := hM
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (s (IsLocalRing.closedPoint Ω)))
  rw [← S.range_immersion] at ha
  obtain ⟨t, rfl⟩ := IsImmersion.exists_comp_eq_of_field (S.immersion a) s ha
  obtain ⟨𝒰, h𝒰⟩ := (isLocallyFinitelyPresented_mapMod_iff _ _ M).1 (hS a)
  have h𝒰' := isFinitelyPresented_upperStar_of_isLocallyFinitelyPresented h𝒰
  rw [Scheme.Hom.comp_apply, mem_stalkZeroLocus_iff_of_isImmersion,
    mem_stalkZeroLocus_iff_fiberRankFun_eq_zero 𝒰 h𝒰']
  exact (isZero_upperStar_iff_fiberRankFun_eq_zero 𝒰 h𝒰' t).1
    (h.of_iso ((upperStarComp _ t (S.immersion a)).app M).symm)

/-- The vanishing locus of a zero module is everything. -/
lemma stalkZeroLocus_eq_univ_of_isZero {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)} (hM : IsZero M) :
    stalkZeroLocus ℓ M = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ s _ ↦ (s)^*⟦_⟧.map_isZero hM

section FiniteType

variable {k : Type u} [Field k] (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom]

/-- On a stratum of a constructible module on a scheme of finite type over a field, the
vanishing locus is open: it is the locus where the (locally constant) fibre rank of the
restriction vanishes. -/
lemma isOpen_preimage_stalkZeroLocus_of_isLocallyFinitelyPresented {T : Scheme.{u}}
    (j : T ⟶ Z.left) [IsImmersion j]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)
      ((j)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) :
    IsOpen (j.base ⁻¹' stalkZeroLocus ℓ M) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : TopologicalSpace.NoetherianSpace T := IsImmersion.noetherianSpace j
  let T' : Over (Spec (.of k)) := Over.mk (j ≫ Z.hom)
  have : LocallyOfFiniteType T'.hom := inferInstanceAs (LocallyOfFiniteType (j ≫ Z.hom))
  have : QuasiCompact T'.hom := inferInstanceAs (QuasiCompact (j ≫ Z.hom))
  have hlc := isLocallyConstant_fiberRankFun (ℓ := ℓ) T' hM
  obtain ⟨𝒰, h𝒰⟩ := hM
  have heq : j.base ⁻¹' stalkZeroLocus ℓ M = fiberRankFun ℓ
      ((j)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) ⁻¹' {0} := by
    ext t
    rw [Set.mem_preimage, mem_stalkZeroLocus_iff_of_isImmersion,
      mem_stalkZeroLocus_iff_fiberRankFun_eq_zero 𝒰
        (isFinitelyPresented_upperStar_of_isLocallyFinitelyPresented h𝒰)]
    rfl
  rw [heq]
  exact hlc.isOpen_fiber 0

/-- **The vanishing locus of a constructible `ℚ̲̄_ℓ`-module is constructible**, on a scheme of
finite type over a field: on each stratum `Xₐ` of a stratification adapted to `M`, it is the
open subset of `Xₐ` where the fibre rank of `M|_{Xₐ}` vanishes, and locally closed subsets of a
noetherian space are constructible. -/
theorem isConstructible_stalkZeroLocus
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left)}
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)
      M) : IsConstructible (stalkZeroLocus ℓ M) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  obtain ⟨S, hS⟩ := hM
  have heq : stalkZeroLocus ℓ M = ⋃ a, (S.stratum a ∩ stalkZeroLocus ℓ M) := by
    rw [← Set.iUnion_inter, S.iUnion_stratum_eq_univ, Set.univ_inter]
  rw [heq]
  refine IsConstructible.iUnion fun a ↦ ?_
  have ho := isOpen_preimage_stalkZeroLocus_of_isLocallyFinitelyPresented Z (S.immersion a)
    ((isLocallyFinitelyPresented_mapMod_iff _ _ M).1 (hS a))
  obtain ⟨O, hO, hOe⟩ := (S.immersion a).isEmbedding.isInducing.isOpen_iff.mp ho
  have : S.stratum a ∩ stalkZeroLocus ℓ M = S.stratum a ∩ O := by
    rw [← S.range_immersion]
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion a).base ⁻¹' O
      rw [hOe]
      exact hx
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion a).base ⁻¹' stalkZeroLocus ℓ M
      rw [← hOe]
      exact hx
  rw [this]
  exact (S.isConstructible_stratum a).inter hO.isConstructible_of_noetherianSpace

end FiniteType

section Complex

variable (ℓ) in
/-- The *vanishing locus* of a complex `K` of `ℚ̲̄_ℓ,X`-modules: the points in the vanishing locus
of every cohomology sheaf `Hⁿ(K)`. -/
def complexStalkZeroLocus {X : Scheme.{u}}
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))) : Set X :=
  ⋂ n : ℤ, stalkZeroLocus ℓ ((DerivedCategory.homologyFunctor _ n).obj K)

/-- **The vanishing locus of a bounded constructible `ℚ̲̄_ℓ`-complex is constructible**, on a
scheme of finite type over a field: it is the intersection of the vanishing loci of the finitely
many nonzero cohomology sheaves, which are constructible. -/
theorem isConstructible_complexStalkZeroLocus {k : Type u} [Field k] (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) K) :
    IsConstructible (complexStalkZeroLocus ℓ K) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  have heq : complexStalkZeroLocus ℓ K = ⋂ n ∈ Set.Icc a b,
      stalkZeroLocus ℓ ((DerivedCategory.homologyFunctor _ n).obj K) := by
    ext x
    simp only [complexStalkZeroLocus, Set.mem_iInter]
    refine ⟨fun h n _ ↦ h n, fun h n ↦ ?_⟩
    by_cases hn : n ∈ Set.Icc a b
    · exact h n hn
    · rw [stalkZeroLocus_eq_univ_of_isZero (hab n (by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hn; exact hn))]
      trivial
  rw [heq]
  exact IsConstructible.biInter (Set.finite_Icc a b) fun n _ ↦
    isConstructible_stalkZeroLocus Z (hc n)

end Complex

end AlgebraicGeometry.ProEtale.CondensedRing
