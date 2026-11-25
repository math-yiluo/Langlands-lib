/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Finite clopen refinements from categorical weak contractibility

Source: Stacks Project, Tag 098F, the section and inverse-image partition argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem section_of_cover {T : Scheme.{t}} {W V : T.ProEt}
    (p : V ⟶ W) (hp : Sieve.generate (Presieve.singleton p) ∈ ProEt.topology T W)
    (hW : ∀ (F G : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f → Function.Surjective (f.hom.app (op W))) :
    ∃ s : W ⟶ V, s ≫ p = 𝟙 W := by
  let J := ProEt.topology T
  have hepi : Epi (J.uliftYoneda.{max u (t + 1)}.map p) := by
    constructor
    intro Z a b hab
    apply J.uliftYonedaEquiv.injective
    have heq : Z.obj.map p.op (J.uliftYonedaEquiv a) =
        Z.obj.map p.op (J.uliftYonedaEquiv b) := by
      rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality, hab]
    apply Sheaf.isSeparated Z W _ hp
    rintro Y f ⟨_, g, _, ⟨⟩, rfl⟩
    simpa only [op_comp, Functor.map_comp, types_comp_apply] using
      congrArg (Z.obj.map g.op) heq
  obtain ⟨s, hs⟩ := hW _ _ (J.uliftYoneda.{max u (t + 1)}.map p) hepi ⟨𝟙 W⟩
  exact ⟨s.down, congrArg ULift.down hs⟩

private theorem refinement_of_split (T : Scheme.{t}) (W : T.ProEt) [IsAffine W.left]
    (hsplit : ∀ (V : Scheme.{t}) [IsAffine V] (p : V ⟶ W.left)
      [WeaklyEtale p] [Surjective p], ∃ s : W.left ⟶ V, s ≫ p = 𝟙 _)
    (S : Sieve W) (hS : S ∈ ProEt.topology T W) :
    ∃ (n : ℕ) (O : Fin n → W.left.Opens),
      (∀ i, IsClosed (O i : Set W.left)) ∧
      Pairwise (fun i j ↦ Disjoint (O i) (O j)) ∧ iSup O = ⊤ ∧
      ∀ i, S (ProEt.ofOpenImmersionHom W (O i).ι) := by
  classical
  obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (ProEt.mem_precoverage_iff.1 hP)
  obtain ⟨𝒱, g, hfin, _⟩ := Cover.QuasiCompact.exists_hom.{t + 1, t} 𝒰
  let := hfin
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget T ⋙ Over.forget T) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  let e : Fin (Nat.card 𝒱.I₀) ≃ 𝒱.I₀ := (Finite.equivFin _).symm
  let V (i : Fin (Nat.card 𝒱.I₀)) := Spec (𝒱.X (e i))
  let v (i : Fin (Nat.card 𝒱.I₀)) := 𝒱.f (e i)
  have (i : Fin (Nat.card 𝒱.I₀)) : IsAffine (V i) := inferInstance
  have : WeaklyEtale (Sigma.desc v) :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦ 𝒱.map_prop (e i)
  have : Surjective (Sigma.desc v) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := e.surjective (𝒱.idx x)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    dsimp only [v]
    rw [hi]
    exact 𝒱.covers x
  obtain ⟨s, hs'⟩ := hsplit (∐ V) (Sigma.desc v)
  let O (i : Fin (Nat.card 𝒱.I₀)) : W.left.Opens := s ⁻¹ᵁ (Sigma.ι V i).opensRange
  have hdis : Pairwise (fun i j ↦ Disjoint (O i) (O j)) := by
    intro i j hij A hi hj x hx
    exact (disjoint_opensRange_sigmaι V i j hij).le_bot ⟨hi hx, hj hx⟩
  have hO : ∀ x : W.left, ∃ i, x ∈ O i := by
    intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    exact ⟨i, y, hy⟩
  have hclosed (i) : IsClosed (O i : Set W.left) := by
    rw [← isOpen_compl_iff]
    have heq : (O i : Set W.left)ᶜ = ⋃ j : {j // j ≠ i}, (O j.1 : Set _) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := hO x
        exact ⟨⟨j, fun hji ↦ hx (hji ▸ hj)⟩, hj⟩
      · rintro ⟨j, hj⟩ hi
        exact (hdis j.2).le_bot ⟨hj, hi⟩
    rw [heq]
    exact isOpen_iUnion fun j ↦ (O j.1).isOpen
  refine ⟨Nat.card 𝒱.I₀, O, hclosed, hdis, ?_, ?_⟩
  · apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr (hO x)
  · intro i
    have hfactor : Set.range ((O i).ι ≫ s).base ⊆ Set.range (Sigma.ι V i).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    let b : (O i).toScheme ⟶ V i :=
      IsOpenImmersion.lift (Sigma.ι V i) ((O i).ι ≫ s) hfactor
    have hb : b ≫ v i = (O i).ι := by
      rw [← Sigma.ι_comp_desc v i, ← Category.assoc, IsOpenImmersion.lift_fac,
        Category.assoc, hs', Category.comp_id]
    have ha' (j : 𝒰.I₀) : (a j).left = eqToHom (hZ j) ≫ 𝒰.f j := hZa j
    let d : (O i).toScheme ⟶ (Z (g.s₀ (e i))).left :=
      b ≫ g.h₀ (e i) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (e i))).left = (O i).ι := by
      rw [ha', Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, g.w₀]
      exact hb
    let d' : ProEt.ofOpenImmersion W (O i).ι ⟶ Z (g.s₀ (e i)) :=
      MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (g.s₀ (e i))), ← Category.assoc, hd]
        rfl)
    have heq : ProEt.ofOpenImmersionHom W (O i).ι = d' ≫ a (g.s₀ (e i)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [heq]
    exact S.downward_closed (hPS _ _ (ha _)) _

/-- A covering sieve on an affine categorical weakly contractible object admits a
finite clopen partition refining it.

Source: Stacks Project, Tag 098F (blueprint: lem-sf-clopen-cover-geometry).
Proof: refine the sieve to finitely many affine opens in covering members. Their
finite coproduct is affine, weakly etale and surjective over the target. The represented
covering morphism is epic, so evaluation lifts the identity to a section. Pull the
coproduct components back along that section. They are disjoint clopens covering the
target, and the restricted section factors each inclusion through the original sieve.
The same construction includes the empty affine scheme and the empty cover. -/
private theorem sf_clopen_cover_refinement (T : Scheme.{t}) (W : T.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f → Function.Surjective (f.hom.app (op W)))
    (S : Sieve W) (hS : S ∈ ProEt.topology T W) :
    ∃ (n : ℕ) (O : Fin n → W.left.Opens),
      (∀ i, IsClosed (O i : Set W.left)) ∧
      Pairwise (fun i j ↦ Disjoint (O i) (O j)) ∧ iSup O = ⊤ ∧
      ∀ i, S (ProEt.ofOpenImmersionHom W (O i).ι) := by
  apply refinement_of_split T W _ S hS
  intro V _ p _ _
  let Q : T.ProEt := ProEt.mk (p ≫ W.hom)
  let a : Q ⟶ W := MorphismProperty.Over.homMk p rfl
  have ha : Sieve.generate (Presieve.singleton a) ∈ ProEt.topology T W := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := p) inferInstance
  obtain ⟨s, hs⟩ := section_of_cover a ha hW
  exact ⟨s.left, congrArg (fun f ↦ f.left) hs⟩

private theorem weak_of_refinement (T : Scheme.{t}) (W : T.ProEt)
    (href : ∀ S ∈ ProEt.topology T W,
      ∃ (n : ℕ) (O : Fin n → W.left.Opens),
        (∀ i, IsClosed (O i : Set W.left)) ∧
        Pairwise (fun i j ↦ Disjoint (O i) (O j)) ∧ iSup O = ⊤ ∧
        ∀ i, S (ProEt.ofOpenImmersionHom W (O i).ι)) :
    ∀ (F G : Sheaf (ProEt.topology T) (Type (max w (t + 1)))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W)) := by
  have h : (ProEt.topology T).IsWeaklyContractible.{max w (t + 1)} W := by
    apply GrothendieckTopology.isWeaklyContractible_of_forall_mem
    intro S hS
    obtain ⟨n, O, _, hd, hc, hm⟩ := href S hS
    refine ⟨ULift.{t} (Fin n), fun i ↦ ProEt.ofOpenImmersion W (O i.down).ι,
      fun i ↦ ProEt.ofOpenImmersionHom W (O i.down).ι, ?_, fun i ↦ hm i.down, ?_, ?_⟩
    · apply ProEt.mem_topology_of_openImmersion _ (fun i : ULift.{t} (Fin n) ↦ (O i.down).ι) _
        (fun i ↦ Sieve.ofArrows_mk _ _ i)
      intro x
      have hx : x ∈ iSup O := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨⟨i⟩, (Opens.range_ι (O i)).symm ▸ hi⟩
    · intro i
      exact (ProEt.forget T ⋙ Over.forget T).mono_of_mono_map
        (inferInstanceAs (Mono (O i.down).ι))
    · intro i j hij Z a b hab
      have hij' : i.down ≠ j.down := fun h ↦ hij (ULift.ext h)
      have : IsEmpty Z.left := by
        constructor
        intro z
        have hab' : a.left ≫ (O i.down).ι = b.left ≫ (O j.down).ι :=
          congrArg (fun g ↦ g.left) hab
        have hi : (a.left ≫ (O i.down).ι).base z ∈ O i.down :=
          (Opens.range_ι (O i.down)).subset ⟨a.left z, rfl⟩
        have hj : (a.left ≫ (O i.down).ι).base z ∈ O j.down := by
          rw [hab']
          exact (Opens.range_ι (O j.down)).subset ⟨b.left z, rfl⟩
        exact (hd hij').le_bot ⟨hi, hj⟩
      exact ProEt.bot_mem_topology Z
  intro F G f hf
  exact h f ((Sheaf.isLocallySurjective_iff_epi f).mpr hf)

private theorem split_clopen_cover (T : Scheme.{t}) [IsAffine T]
    (hT : ∀ (F G : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 T)))))
    (U : T.Opens) (hU : IsClosed (U : Set T))
    (V : Scheme.{t}) [IsAffine V] (p : V ⟶ U.toScheme)
    [WeaklyEtale p] [Surjective p] :
    ∃ s : U.toScheme ⟶ V, s ≫ p = 𝟙 _ := by
  classical
  let Z : T.Opens := ⟨(U : Set T)ᶜ, hU.isOpen_compl⟩
  have : IsClosedImmersion Z.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa [Z] using U.isOpen.isClosed_compl)
  have : IsAffine Z.toScheme := isAffine_of_isAffineHom Z.ι
  let Y : Bool → Scheme.{t} := fun b ↦ if b then Z.toScheme else V
  let q : ∀ b, Y b ⟶ T := fun b ↦ by
    cases b
    · exact p ≫ U.ι
    · exact Z.ι
  have (b : Bool) : IsAffine (Y b) := by cases b <;> assumption
  have (b : Bool) : WeaklyEtale (q b) := by cases b <;> dsimp [q] <;> infer_instance
  have : WeaklyEtale (Sigma.desc q) := IsZariskiLocalAtSource.sigmaDesc inferInstance
  have : Surjective (Sigma.desc q) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨y, hy⟩ := p.surjective ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨false, y, by change U.ι (p y) = x; rw [hy]; rfl⟩
    · exact Set.mem_iUnion.mpr ⟨true, ⟨x, hx⟩, rfl⟩
  let Q : T.ProEt := ProEt.mk (Sigma.desc q)
  let a : Q ⟶ ProEt.mk (𝟙 T) := MorphismProperty.Over.homMk (Sigma.desc q)
      (by change Sigma.desc q ≫ 𝟙 T = Sigma.desc q; simp)
  have ha : Sieve.generate (Presieve.singleton a) ∈ ProEt.topology T _ := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
      (f := Sigma.desc q) inferInstance
  obtain ⟨s, hs⟩ := section_of_cover a ha hT
  have hs' : s.left ≫ Sigma.desc q = 𝟙 T := congrArg (fun f ↦ f.left) hs
  have hf : Set.range (U.ι ≫ s.left).base ⊆ Set.range (Sigma.ι Y false).base := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, y, hy⟩ := (sigmaOpenCover Y).exists_eq ((U.ι ≫ s.left) x)
    change (Sigma.ι Y b) y = (U.ι ≫ s.left) x at hy
    cases b
    · exact ⟨y, hy⟩
    · have heq : Z.ι y = U.ι x := by
        have hq : Sigma.ι Y true ≫ Sigma.desc q = Z.ι := Sigma.ι_comp_desc q true
        exact (congrArg (fun f ↦ f y) hq).symm.trans
          ((congrArg (fun z ↦ (Sigma.desc q) z) hy).trans
            (congrArg (fun f ↦ f (U.ι x)) hs'))
      apply False.elim
      apply y.2
      change (Z.ι y) ∈ (U : Set T)
      rw [heq]
      exact x.2
  let r : U.toScheme ⟶ V := IsOpenImmersion.lift (Sigma.ι Y false) (U.ι ≫ s.left) hf
  refine ⟨r, (cancel_mono U.ι).mp ?_⟩
  change r ≫ q false = 𝟙 _ ≫ U.ι
  rw [← Sigma.ι_comp_desc q false, ← Category.assoc, IsOpenImmersion.lift_fac,
    Category.assoc, hs', Category.comp_id, Category.id_comp]

/-- A clopen of an affine categorically weakly contractible scheme is weakly
contractible in every coefficient universe.

Source: Stacks Project, Tags 098F and 090M
(blueprint: lem-sf-clopen-weak-contractibility).
Proof: an affine surjective weakly etale cover of the clopen is augmented by its
clopen complement to an affine cover of the whole scheme. Lift the identity through
its represented epimorphism, then restrict the section to the original component.
Every covering sieve of the clopen therefore has a finite disjoint open refinement.
The sheaf gluing axiom glues local lifts across that disjoint cover in any universe.
This includes empty clopens, since the empty family glues the unique empty section. -/
private theorem sf_clopen_weak_contractibility (T : Scheme.{t}) [IsAffine T]
    (hT : ∀ (F G : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 T)))))
    (U : T.Opens) (hU : IsClosed (U : Set T)) :
    ∀ (F G : Sheaf (ProEt.topology U.toScheme) (Type (max w (t + 1)))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 U.toScheme)))) := by
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa only [Opens.range_ι] using hU)
  have : IsAffine U.toScheme := isAffine_of_isAffineHom U.ι
  have : IsAffine (ProEt.mk (𝟙 U.toScheme)).left := ‹IsAffine U.toScheme›
  apply weak_of_refinement U.toScheme (ProEt.mk (𝟙 U.toScheme))
  intro S hS
  apply refinement_of_split U.toScheme (ProEt.mk (𝟙 U.toScheme)) _ S hS
  intro V _ p _ _
  exact split_clopen_cover T hT U hU V p

/-- Categorical weak contractibility gives finite clopen refinements and is inherited
by every clopen component, in any coefficient universe.

Source: Stacks Project, Tags 098F and 090M
(blueprint: lem-sf-clopen-cover-geometry).
Proof: refine a covering sieve of the affine target to finitely many affine members.
Their represented coproduct covering is epic, so evaluation lifts the identity to a
section. Its inverse images of the coproduct summands form a finite clopen partition
refining the sieve. For a cover of a clopen, adjoin its affine clopen complement and
split the resulting cover of the whole target. Restricting that section splits the
original cover. Finite disjoint refinements then glue local lifts of sheaf sections,
independently of their universe. Empty covers and empty clopens are included. -/
theorem sf_clopen_cover_geometry (T : Scheme.{t}) [IsAffine T]
    (hT : ∀ (F G : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 T))))) :
    (∀ S ∈ ProEt.topology T (ProEt.mk (𝟙 T)),
      ∃ (n : ℕ) (O : Fin n → T.Opens),
        (∀ i, IsClosed (O i : Set T)) ∧
        Pairwise (fun i j ↦ Disjoint (O i) (O j)) ∧ iSup O = ⊤ ∧
        ∀ i, S (ProEt.ofOpenImmersionHom (ProEt.mk (𝟙 T)) (O i).ι)) ∧
    (∀ (U : T.Opens), IsClosed (U : Set T) →
      ∀ (F G : Sheaf (ProEt.topology U.toScheme) (Type (max w (t + 1))))
        (f : F ⟶ G), Epi f →
          Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 U.toScheme))))) := by
  have : IsAffine (ProEt.mk (𝟙 T)).left := ‹IsAffine T›
  exact ⟨sf_clopen_cover_refinement T (ProEt.mk (𝟙 T)) hT,
    sf_clopen_weak_contractibility T hT⟩

end WeilConjectures
