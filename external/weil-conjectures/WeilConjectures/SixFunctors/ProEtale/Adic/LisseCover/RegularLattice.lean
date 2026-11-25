/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedFiniteEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedPullback

/-!
# Lattices of lisse sheaves on regular schemes

Let `T` be a regular Noetherian scheme, `f : V ⟶ T` a single-morphism pro-étale cover and
`γ : V ×_T V → GL_n(E)` a cocycle acting on the lattices of `Eⁿ` by a descent cocycle (the
transition cocycle of a trivialisation of a lisse sheaf,
`AlgebraicGeometry.ProEtale.AdicSheaf.isDescentCocycle_smul_compactOpenLattice`). Then `γ` has a
twisted section with values in the lattices
(`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice`): a lisse sheaf on a regular
scheme has a lattice (blueprint `proposition-lattices-representations-normal-scheme` (4), used in
`theorem-purity-higher-direct-images-under`).

On a connected `T`, the orbit of a lattice is contained in a finite invariant set of lattices
(`AlgebraicGeometry.exists_finite_invariant_subset`, Bhatt–Scholze, Lemma 7.4.10), whose sum is an
invariant lattice. In general the sections over the finitely many connected components glue.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E] {n : ℕ} {T V : Scheme.{u}}

/-- **Lattices on connected regular schemes.** -/
theorem exists_isTwistedSection_compactOpenLattice_of_connectedSpace [IsLocallyNoetherian T]
    [CompactSpace T] [IsRegular T] [ConnectedSpace T] (f : V ⟶ T) [WeaklyEtale f]
    [Surjective f] [QuasiCompact f] (γ : ↥(pullback f f) → GL (Fin n) E)
    (hc : IsDescentCocycle f (fun z (L : CompactOpenLattice E n) ↦ γ z • L)) :
    ∃ σ, IsTwistedSection f (fun z (L : CompactOpenLattice E n) ↦ γ z • L) (𝟙 T) σ := by
  classical
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  obtain ⟨v₀, -⟩ := f.surjective t₀
  obtain ⟨A, hAfin, hAlc, hAinv, hs⟩ :=
    exists_finite_invariant_subset f hc v₀ (CompactOpenLattice.standard E n)
  set p₁ := (pullback.fst f f).base
  set p₂ := (pullback.snd f f).base
  set q := (pullback.fst f (𝟙 T)).base
  have hq : Function.Surjective q := (pullback.fst f (𝟙 T)).surjective
  -- `A` is nonempty everywhere
  have hne (w : V) : (A w).Nonempty := by
    have key := IsTwistedSection.apply_eq_of_preconnectedSpace (f := f) (𝟙 T)
      (fun x ↦ (A (q x)).Nonempty)
      ((hAlc.comp _).comp_continuous (pullback.fst f (𝟙 T)).base.hom.continuous)
      (fun w ↦ by
        have h := hAinv ((twistedPairMap f (𝟙 T)).base w)
        simp only [p₁, p₂, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_snd] at h
        simp only [q, Scheme.Hom.comp_apply] at h ⊢
        rw [h, Set.image_nonempty])
    obtain ⟨x, hx⟩ := hq w
    obtain ⟨x₀, hx₀⟩ := hq v₀
    have := key x x₀
    simp only [hx, hx₀, eq_iff_iff] at this
    exact this.2 ⟨_, hs⟩
  -- the sum of the lattices of `A`
  let sumL (B : Set (CompactOpenLattice E n)) : CompactOpenLattice E n :=
    if h : B.Finite ∧ B.Nonempty then
      CompactOpenLattice.sum h.1.toFinset (h.1.toFinset_nonempty.2 h.2)
    else CompactOpenLattice.standard E n
  have hsumL (w : V) : sumL (A w) = CompactOpenLattice.sum (hAfin w).toFinset
      ((hAfin w).toFinset_nonempty.2 (hne w)) := by
    simp only [sumL, dite_eq_left (And.intro (hAfin w) (hne w))]
  refine ⟨fun x ↦ sumL (A (q x)), ?_, fun w ↦ ?_⟩
  · exact (hAlc.comp sumL).comp_continuous (pullback.fst f (𝟙 T)).base.hom.continuous
  · set z := (twistedPairMap f (𝟙 T)).base w
    have h := hAinv z
    have e₁ : p₁ z = q ((pullback.fst (pullback.snd f (𝟙 T)) (pullback.snd f (𝟙 T))).base w) := by
      simp only [z, p₁, q, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    have e₂ : p₂ z = q ((pullback.snd (pullback.snd f (𝟙 T)) (pullback.snd f (𝟙 T))).base w) := by
      simp only [z, p₂, q, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [e₁, e₂] at h
    change sumL (A _) = γ z • sumL (A _)
    rw [hsumL, hsumL, CompactOpenLattice.smul_sum]
    congr 1
    ext L
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, h, Set.mem_image]

/-- **Lattices on regular schemes.** Let `T` be a regular Noetherian scheme and `γ` a cocycle
on a single-morphism pro-étale cover of `T` acting on the lattices of `Eⁿ` by a descent cocycle.
Then `γ` has a twisted section with values in the lattices. -/
theorem exists_isTwistedSection_compactOpenLattice [IsLocallyNoetherian T] [CompactSpace T]
    [IsRegular T] (f : V ⟶ T) [WeaklyEtale f] [Surjective f] [QuasiCompact f]
    (γ : ↥(pullback f f) → GL (Fin n) E)
    (hc : IsDescentCocycle f (fun z (L : CompactOpenLattice E n) ↦ γ z • L)) :
    ∃ σ, IsTwistedSection f (fun z (L : CompactOpenLattice E n) ↦ γ z • L) (𝟙 T) σ := by
  classical
  have : IsNoetherian T := ⟨⟩
  obtain ⟨N, U, hUc, hUd, hUcov, hUi⟩ := IsRegular.exists_isClopen_isIntegral T
  let c := fun z (L : CompactOpenLattice E n) ↦ γ z • L
  -- a section over each piece
  have hsec (a : Fin N) : ∃ σ, IsTwistedSection f c (U a).ι σ := by
    have := (hUi a).1
    have : IsRegular (U a).toScheme :=
      ⟨isRegularLocalRing_stalk_of_etale (U a).ι fun y ↦ inferInstance⟩
    have : CompactSpace (U a).toScheme := isCompact_iff_compactSpace.1 (hUc a).1.isCompact
    obtain ⟨σ, hσ⟩ := exists_isTwistedSection_compactOpenLattice_of_connectedSpace
        (pullback.snd f (U a).ι) (fun w ↦ γ ((twistedPairMap f (U a).ι).base w))
        (hc.pullbackCover (U a).ι)
    exact ⟨_, hσ.ofPullbackCover⟩
  choose σ hσ using hsec
  -- glue along the étale cover by the pieces
  let Ui (a : Fin N) : T.Etale := Scheme.Etale.mk (U a).ι
  let πi (a : Fin N) : Ui a ⟶ Scheme.Etale.mk (𝟙 T) :=
    MorphismProperty.Over.homMk (U a).ι (Category.comp_id _) trivial
  have hcov (t : T) : ∃ a, ∃ x, (πi a).left.base x = t := by
    have : t ∈ (⨆ a, U a : T.Opens) := by rw [hUcov]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨a, ⟨t, ha⟩, rfl⟩
  have hsheaf := isSheafFor_ofArrows_twistedSectionsPresheaf f c Ui πi hcov
  rw [Presieve.isSheafFor_arrows_iff] at hsheaf
  refine (hsheaf (fun a ↦ ⟨σ a, hσ a⟩) ?_).exists.elim fun s _ ↦ ⟨s.1, s.2⟩
  intro a b W ga gb h
  by_cases hab : a = b
  · subst hab
    have : ga = gb := by
      apply MorphismProperty.Over.Hom.ext
      exact (cancel_mono (U a).ι).1 (by have := congrArg (fun g ↦ g.left) h; exact this)
    rw [this]
  · have hW : IsEmpty W.left := by
      refine ⟨fun w ↦ ?_⟩
      have h' : ga.left ≫ (U a).ι = gb.left ≫ (U b).ι := by
        have := congrArg (fun g ↦ g.left) h; exact this
      have h'' := congrArg (fun g ↦ g.base w) h'
      simp only [Scheme.Hom.comp_apply] at h''
      have h₁ : (U a).ι.base (ga.left.base w) ∈ U a := by simp
      have h₂ : (U a).ι.base (ga.left.base w) ∈ U b := by
        rw [show (U a).ι.base (ga.left.base w) = (U b).ι.base (gb.left.base w) from h'']; simp
      have := (hUd hab).le_bot (show _ ∈ U a ⊓ U b from ⟨h₁, h₂⟩)
      simp at this
    have : IsEmpty ↥(pullback f W.hom) :=
      ⟨fun x ↦ hW.false ((pullback.snd f W.hom).base x)⟩
    exact Subtype.ext (funext fun x ↦ isEmptyElim x)

/-- **Lattices over regular schemes.** For a cocycle `γ` on a single-morphism pro-étale cover
`f : V ⟶ X` acting on the lattices of `Eⁿ` by a descent cocycle, and any morphism `π : Z ⟶ X`
from a regular Noetherian scheme, `γ` has a lattice-valued twisted section over `π`. -/
theorem exists_isTwistedSection_compactOpenLattice_of_isRegular {X : Scheme.{u}} (f : V ⟶ X)
    [WeaklyEtale f] [Surjective f] [QuasiCompact f] (γ : ↥(pullback f f) → GL (Fin n) E)
    (hc : IsDescentCocycle f (fun z (L : CompactOpenLattice E n) ↦ γ z • L)) {Z : Scheme.{u}}
    (π : Z ⟶ X) [IsRegular Z] [IsLocallyNoetherian Z] [CompactSpace Z] :
    ∃ σ, IsTwistedSection f (fun z (L : CompactOpenLattice E n) ↦ γ z • L) π σ := by
  obtain ⟨σ, hσ⟩ := exists_isTwistedSection_compactOpenLattice (pullback.snd f π)
    (fun w ↦ γ ((twistedPairMap f π).base w)) (hc.pullbackCover π)
  exact ⟨_, hσ.ofPullbackCover⟩

end AlgebraicGeometry
