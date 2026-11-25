/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.Topology.Sober
public import WeilConjectures.WeilSheaf.Category

/-!
# The lisse locus of a Weil sheaf

A Weil sheaf on a reduced `k₀`-scheme of finite type is lisse on a dense open subscheme
(generic lissity, used in blueprint `proposition-relative-affine-line--1`).

## Main results

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_forall_exists_opens`: lissity is local for
  the Zariski topology.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf`: on a
  reduced scheme whose underlying space is Noetherian, a constructible sheaf is lisse near each
  generic point of an irreducible component.
- `AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`: generic lissity of Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.isLisse_upperStar_comp_iff`,
  `AlgebraicGeometry.WeilSheaf.IsLisse.upperStar_opensι_preimage`: lissity of iterated pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- **Lissity is Zariski local.** If every point of `X` has an open neighbourhood on which `F`
is lisse, then `F` is lisse: the composites of the trivialising covers with the open cover form a
pro-étale covering family. -/
theorem IsAdicLisseSheaf.of_forall_exists_opens {F : AdicSheaf l X}
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F)) :
    IsAdicLisseSheaf F := by
  choose W hxW hW using h
  choose R hR hRF using hW
  choose σ V g hg using fun x ↦ (R x).exists_eq_ofArrows
  have hcov : Presieve.ofArrows (fun x ↦ (W x).toScheme) (fun x ↦ (W x).ι) ∈
      Scheme.proetalePrecoverage X :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ ⟨x, by simpa using hxW x⟩, fun x ↦ inferInstance⟩)
  refine ⟨_, Precoverage.comp_mem_coverings (fun x ↦ (W x).ι) hcov g
    (fun x ↦ hg x ▸ hR x), ?_⟩
  rintro _ _ ⟨⟨x, j⟩⟩
  obtain ⟨n, ⟨e⟩⟩ := hRF x (g x j) (by rw [hg x]; exact .mk j)
  exact ⟨n, ⟨(adicUpperStarComp l _ _).app F ≪≫ e⟩⟩

/-- On a reduced scheme, the restriction of a sheaf to an open subscheme contained in the image
of an immersion `f` on which the sheaf is lisse, is lisse: the open subscheme is isomorphic to its
preimage under `f`, the restriction of `f` being a surjective closed immersion onto a reduced
scheme. -/
theorem IsAdicLisseSheaf.upperStar_opensι_of_subset_range [IsReduced X] {F : AdicSheaf l X}
    {Z : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (hf : IsAdicLisseSheaf ((f)^*ᵃ[l].obj F))
    (W : X.Opens) (hW : (W : Set X) ⊆ Set.range f) :
    IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F) := by
  have hsurj : Surjective (f ∣_ W) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨z, hz⟩ := hW y.2
    exact ⟨⟨z, show f z ∈ W from hz ▸ y.2⟩, Subtype.ext (by simp [hz])⟩
  have : IsClosedImmersion (f ∣_ W) := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    rw [Set.range_eq_univ.2 hsurj.surj]
    exact isClosed_univ
  have : IsIso (f ∣_ W) := isIso_of_isClosedImmersion_of_surjective _
  have heq : W.ι = (inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι) ≫ f := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  exact ((hf.upperStar (inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι)).of_iso
    ((adicUpperStarComp l _ _).app F).symm).of_iso ((adicUpperStarCongr l heq.symm).app F)

/-- **Generic lissity of constructible sheaves.** On a reduced scheme whose underlying space is
Noetherian, a constructible `ℓ`-adic sheaf is lisse on an open neighbourhood of every generic
point of an irreducible component: the stratum through the generic point has constructible image,
hence contains an open neighbourhood of it. -/
theorem IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf [IsReduced X]
    [TopologicalSpace.NoetherianSpace X] {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F)
    {ξ : X} (hξ : ξ ∈ genericPoints X) :
    ∃ W : X.Opens, ξ ∈ W ∧ IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F) := by
  obtain ⟨W, j, hj, ⟨w, rfl⟩, ι', hι', Z, i, hi, -, hcover, hl⟩ := hF ξ
  obtain ⟨k, ⟨z, hz⟩, -⟩ := hcover w
  have hs : IsConstructible (Set.range (i k ≫ j)) :=
    (i k ≫ j).isLocallyClosed_range.isConstructible_of_noetherianSpace
  obtain ⟨u, hu, hξu, hus⟩ := hs.exists_isOpen_mem_subset hξ ⟨z, by simp [hz]⟩
  exact ⟨⟨u, hu⟩, hξu, IsAdicLisseSheaf.upperStar_opensι_of_subset_range (i k ≫ j)
    ((hl k).of_iso ((adicUpperStarComp l _ _).app F).symm) ⟨u, hu⟩ hus⟩

end ProEtale

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Generic lissity.** A Weil sheaf on a reduced `k₀`-scheme of finite type is lisse on a dense
open subscheme (blueprint: `proposition-relative-affine-line--1`, the lissity loci chosen over
the finite-field model). -/
theorem WeilSheaf.exists_dense_isLisse_upperStar {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsReduced X] (F : WeilSheaf k₀ l X) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ ((WeilSheaf.upperStar U.ι).obj F).IsLisse := by
  set f := X ↘ Spec (CommRingCat.of k₀)
  set p := f.geometricFiberProj
  -- the geometric fibre is reduced, with Noetherian underlying space
  have : GeometricallyReduced f := GeometricallyReduced.of_perfectField f
  have : IsReduced f.geometricFiber :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced _ _
  have : IsNoetherian f.geometricFiber := {}
  have : IsIntegralHom p := by
    have : IsIntegralHom (Scheme.specAlgebraicClosure k₀).hom := by
      change IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀))))
      rw [IsIntegralHom.SpecMap_iff]
      exact Algebra.IsIntegral.isIntegral (R := k₀) (A := AlgebraicClosure k₀)
    exact inferInstanceAs (IsIntegralHom (Limits.pullback.fst _ _))
  -- the lisse locus `L` of `F` on the geometric fibre, and its closed complement `T`
  set L : Set f.geometricFiber := {x | ∃ W : f.geometricFiber.Opens, x ∈ W ∧
    ProEtale.IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F.carrier)}
  have hL : IsOpen L := isOpen_iff_forall_mem_open.2 fun x ⟨W, hxW, hW⟩ ↦
    ⟨W, fun y hy ↦ ⟨W, hy, hW⟩, W.isOpen, hxW⟩
  have hT : IsClosed (p '' Lᶜ) := p.isClosedMap _ hL.isClosed_compl
  refine ⟨⟨(p '' Lᶜ)ᶜ, hT.isOpen_compl⟩, dense_of_genericPoints_subset fun η hη ↦ ?_, ?_⟩
  · -- a point over a generic point of `X` is a generic point of the geometric fibre
    rintro ⟨t, ht, rfl⟩
    refine ht (F.isAdicConstructibleSheaf_carrier.exists_opens_isAdicLisseSheaf
      (mem_genericPoints_iff_forall_specializes.2 fun y hy ↦ ?_))
    exact p.eq_of_specializes_of_apply_eq_of_isIntegralHom hy
      (mem_genericPoints_iff_forall_specializes.1 hη _ (hy.map p.continuous))
  · set U : X.Opens := ⟨(p '' Lᶜ)ᶜ, hT.isOpen_compl⟩
    set g := Scheme.Hom.geometricFiberMap U.ι (comp_over _ (Spec (CommRingCat.of k₀)))
    change ProEtale.IsAdicLisseSheaf ((g)^*ᵃ[l].obj F.carrier)
    refine ProEtale.IsAdicLisseSheaf.of_forall_exists_opens fun y ↦ ?_
    have hy : g y ∈ L := by
      by_contra hy
      have h := congrArg (fun φ ↦ φ y) (Scheme.Hom.geometricFiberMap_comp_geometricFiberProj
        U.ι (comp_over _ (Spec (CommRingCat.of k₀))))
      simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at h
      exact (Scheme.Hom.geometricFiberProj _ y).2 ⟨g y, hy, h⟩
    obtain ⟨W, hyW, hW⟩ := hy
    refine ⟨g ⁻¹ᵁ W, hyW, ?_⟩
    have h₁ := hW.upperStar (g ∣_ W)
    have h₂ : ProEtale.IsAdicLisseSheaf ((g ∣_ W ≫ W.ι)^*ᵃ[l].obj F.carrier) :=
      h₁.of_iso ((ProEtale.adicUpperStarComp l (g ∣_ W) W.ι).app F.carrier).symm
    have h₃ : ProEtale.IsAdicLisseSheaf (((g ⁻¹ᵁ W).ι ≫ g)^*ᵃ[l].obj F.carrier) :=
      h₂.of_iso ((ProEtale.adicUpperStarCongr l (morphismRestrict_ι g W)).app F.carrier)
    exact h₃.of_iso ((ProEtale.adicUpperStarComp l (g ⁻¹ᵁ W).ι g).app F.carrier)

namespace WeilSheaf

variable {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]

/-- The pullback of a lisse Weil sheaf is lisse. -/
theorem IsLisse.upperStar {F : WeilSheaf k₀ l Y} (hF : F.IsLisse) (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] : ((WeilSheaf.upperStar φ).obj F).IsLisse :=
  ProEtale.IsAdicLisseSheaf.upperStar _ hF

/-- Lissity of a pullback only depends on the morphism. -/
theorem isLisse_upperStar_congr {φ φ' : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') (F : WeilSheaf k₀ l Y) :
    ((WeilSheaf.upperStar φ).obj F).IsLisse ↔ ((WeilSheaf.upperStar φ').obj F).IsLisse := by
  have e : Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))) =
      Scheme.Hom.geometricFiberMap φ' (comp_over φ' (Spec (CommRingCat.of k₀))) := by
    subst h
    rfl
  exact ⟨fun h ↦ ProEtale.IsAdicLisseSheaf.of_iso ((ProEtale.adicUpperStarCongr l e).app _) h,
    fun h ↦ ProEtale.IsAdicLisseSheaf.of_iso ((ProEtale.adicUpperStarCongr l e).symm.app _) h⟩

/-- The pullback along a composite is lisse if and only if the iterated pullback is: on
underlying sheaves the two are isomorphic. -/
theorem isLisse_upperStar_comp_iff (φ : X ⟶ Y) (ψ : Y ⟶ Z) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [ψ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Z) :
    ((WeilSheaf.upperStar (φ ≫ ψ)).obj F).IsLisse ↔
      ((WeilSheaf.upperStar φ).obj ((WeilSheaf.upperStar ψ).obj F)).IsLisse := by
  have e := Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ (Spec (CommRingCat.of k₀)))
    (comp_over ψ (Spec (CommRingCat.of k₀)))
  let i := (ProEtale.adicUpperStarCongr l e).app F.carrier ≪≫
    (ProEtale.adicUpperStarComp l _ _).app F.carrier
  exact ⟨fun h ↦ ProEtale.IsAdicLisseSheaf.of_iso i h,
    fun h ↦ ProEtale.IsAdicLisseSheaf.of_iso i.symm h⟩

/-- If the pullback of `G` along `n : A ⟶ B` is lisse on an open `U` of `A`, then the pullback
of `G` along `m ≫ n` is lisse on the preimage of `U` under `m`. -/
theorem IsLisse.upperStar_opensι_preimage {P A B : Scheme.{u}} [P.Over (Spec (CommRingCat.of k₀))]
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))] (U : A.Opens)
    (m : P ⟶ A) (n : A ⟶ B) (n' : P ⟶ B) [m.IsOver (Spec (CommRingCat.of k₀))]
    [n.IsOver (Spec (CommRingCat.of k₀))] [n'.IsOver (Spec (CommRingCat.of k₀))]
    (hmn : m ≫ n = n') {G : WeilSheaf k₀ l B}
    (hU : ((WeilSheaf.upperStar U.ι).obj ((WeilSheaf.upperStar n).obj G)).IsLisse) :
    ((WeilSheaf.upperStar (m ⁻¹ᵁ U).ι).obj ((WeilSheaf.upperStar n').obj G)).IsLisse := by
  have : (m ∣_ U).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over U.ι, morphismRestrict_ι_assoc, comp_over m, comp_over (m ⁻¹ᵁ U).ι]⟩
  have h₁ := (isLisse_upperStar_comp_iff U.ι n G).2 hU
  have h₂ := (isLisse_upperStar_comp_iff (m ∣_ U) _ G).2 (h₁.upperStar (m ∣_ U))
  refine (isLisse_upperStar_comp_iff (m ⁻¹ᵁ U).ι n' G).1
    ((isLisse_upperStar_congr ?_ G).1 h₂)
  rw [morphismRestrict_ι_assoc, hmn]

end WeilSheaf

end AlgebraicGeometry
