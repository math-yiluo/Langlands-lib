/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.SixFunctors.Etale.Gabber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Dévissage for the comparison maps on étale cohomology

For a morphism of schemes `f : X ⟶ Y`, the class of abelian sheaves `G` on `Y` for which every
comparison map `cohomologyMap f G q : Hᵠ(Y, G) ⟶ Hᵠ(X, f^* G)` is bijective is closed under
extensions (by the five lemma in the long exact cohomology sequences) and, when `X` and `Y` are
quasi-compact and quasi-separated, under filtered colimits. Consequently, if it contains every
sheaf killed by a prime, it contains every torsion sheaf.

## Main statements

- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_shortExact`: two out of three.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_isColimit`: filtered colimits.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_nsmul_eq_zero`: sheaves killed by an
  integer, from sheaves killed by a prime.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_isTorsion`: torsion sheaves, from
  sheaves killed by a prime.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The map on cohomology induced by an isomorphism of sheaves is bijective. -/
lemma bijective_sheafHMap_hom {Z : Scheme.{u}}
    {G G' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : G ≅ G') (n : ℕ) : Function.Bijective (Sheaf.H.map e.hom n) :=
  ⟨injective_sheafHMap_of_isIso _ n, fun y ↦ ⟨Sheaf.H.map e.inv n y, by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]⟩⟩

/-- Bijectivity of the comparison maps is invariant under isomorphisms of sheaves. -/
lemma bijective_cohomologyMap_of_iso {G G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : G ≅ G') (q : ℕ) (h : Function.Bijective (cohomologyMap f G q)) :
    Function.Bijective (cohomologyMap f G' q) := by
  have : ⇑(cohomologyMap f G' q) = Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).mapIso e).hom q ∘
      cohomologyMap f G q ∘ Sheaf.H.map e.symm.hom q := by
    ext x
    simp only [Function.comp_apply, Functor.mapIso_hom, ← cohomologyMap_map,
      ← Sheaf.H.map_comp_apply, Iso.symm_hom, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  rw [this]
  exact (bijective_sheafHMap_hom _ q).comp (h.comp (bijective_sheafHMap_hom _ q))

/-- **Two out of three.** For a short exact sequence `0 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 0` of abelian
sheaves on `Y`, if the comparison maps `Hᵠ(Y, Gᵢ) ⟶ Hᵠ(X, f^* Gᵢ)` are bijective in every degree
for `i = 1, 3`, then so are those for `G₂`, by the five lemma. -/
theorem bijective_cohomologyMap_of_shortExact
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₁ : ∀ q, Function.Bijective (cohomologyMap f S.X₁ q))
    (h₃ : ∀ q, Function.Bijective (cohomologyMap f S.X₃ q)) (q : ℕ) :
    Function.Bijective (cohomologyMap f S.X₂ q) := by
  have hS₀ := hS.map_of_exact ((f)^*[AddCommGrpCat.{u + 1}])
  have : Mono (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) := hS₀.mono_f
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : x.comp (Ext.mk₀ S.g) (add_zero q) = 0 := (h₃ q).1 (by
      rw [cohomologyMap_comp_mk₀, hx, Ext.zero_comp, map_zero])
    obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x h3
    rw [cohomologyMap_comp_mk₀] at hx
    cases q with
    | zero =>
      have hx₁ : cohomologyMap f S.X₁ 0 x₁ = 0 := by
        obtain ⟨a, ha⟩ := Ext.homEquiv₀.symm.surjective (cohomologyMap f S.X₁ 0 x₁)
        rw [← ha] at hx ⊢
        rw [Ext.homEquiv₀_symm_apply] at hx ⊢
        rw [Ext.mk₀_comp_mk₀, Ext.mk₀_eq_zero_iff] at hx
        rw [Ext.mk₀_eq_zero_iff]
        exact (cancel_mono _).1 (hx.trans (zero_comp).symm)
      rw [(h₁ 0).1 (hx₁.trans (map_zero _).symm), Ext.zero_comp]
    | succ n =>
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS₀ _ hx rfl
      obtain ⟨z, rfl⟩ := (h₃ n).2 y
      rw [← (h₁ (n + 1)).1 ((cohomologyMap_comp_extClass f hS z).trans hy),
        Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  · obtain ⟨x₃, hx₃⟩ := (h₃ q).2 (y.comp (Ext.mk₀ (((f)^*[AddCommGrpCat.{u + 1}]).map S.g))
      (add_zero q))
    have hδ : x₃.comp hS.extClass rfl = 0 := (h₁ (q + 1)).1 (by
      refine (cohomologyMap_comp_extClass f hS x₃).trans ?_
      rw [map_zero, hx₃]
      refine (Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans ?_
      have : (Ext.mk₀ (S.map (f)^*[AddCommGrpCat.{u + 1}]).g).comp hS₀.extClass (zero_add 1) =
        0 := hS₀.comp_extClass
      exact (congrArg (fun t ↦ y.comp t (show q + 1 = q + 1 from rfl)) this).trans
        (Ext.comp_zero _ _ _ _ _))
    obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₃ rfl hδ
    rw [cohomologyMap_comp_mk₀] at hx₃
    have hy : (y - cohomologyMap f S.X₂ q x₂).comp
        (Ext.mk₀ (((f)^*[AddCommGrpCat.{u + 1}]).map S.g)) (add_zero q) = 0 := by
      rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, hx₃, add_neg_cancel]
    obtain ⟨y₁, hy₁⟩ := Ext.covariant_sequence_exact₂ _ hS₀ _ hy
    obtain ⟨x₁, rfl⟩ := (h₁ q).2 y₁
    refine ⟨x₂ + x₁.comp (Ext.mk₀ S.f) (add_zero q), ?_⟩
    rw [map_add, cohomologyMap_comp_mk₀]
    erw [hy₁]
    rw [add_sub_cancel]

/-- **Sheaves killed by an integer.** If the comparison maps along `f` are bijective in every
degree for every abelian sheaf killed by a prime, they are bijective for every abelian sheaf
killed by a positive integer `n`: by induction on `n`, using the extension
`0 ⟶ G[p] ⟶ G ⟶ G/G[p] ⟶ 0` for a prime `p ∣ n`, whose quotient is killed by `n / p`. -/
theorem bijective_cohomologyMap_of_nsmul_eq_zero
    (hp : ∀ (p : ℕ) (_ : p.Prime) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}),
      p • 𝟙 G = 0 → ∀ q, Function.Bijective (cohomologyMap f G q))
    (n : ℕ) (hn : 0 < n) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : n • 𝟙 G = 0) (q : ℕ) : Function.Bijective (cohomologyMap f G q) := by
  induction n using Nat.strong_induction_on generalizing G q with
  | _ n ih =>
  obtain rfl | hn1 := (Nat.one_le_iff_ne_zero.2 hn.ne').eq_or_lt
  · refine hp 2 Nat.prime_two G ?_ q
    rw [one_nsmul] at hG
    rw [hG, nsmul_zero]
  set p := n.minFac
  have hpp : p.Prime := Nat.minFac_prime hn1.ne'
  obtain ⟨m, hm⟩ : p ∣ n := Nat.minFac_dvd n
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left (hm ▸ hn)
  have hmn : m < n := by
    rw [hm]
    exact lt_mul_left hm0 hpp.one_lt
  let ι := kernel.ι (p • 𝟙 G)
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  refine bijective_cohomologyMap_of_shortExact f hS (hp p hpp _ ?_) (ih m hmn hm0 _ ?_) q
  · rw [← cancel_mono ι, zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      show p • ι = ι ≫ (p • 𝟙 G) by rw [Preadditive.comp_nsmul, Category.comp_id]]
    exact kernel.condition _
  · have h0 : (m • 𝟙 G) ≫ (p • 𝟙 G) = 0 := by
      rw [Preadditive.nsmul_comp, Category.id_comp, ← mul_nsmul, ← hm, hG]
    rw [← cancel_epi (cokernel.π ι), comp_zero, Preadditive.comp_nsmul, Category.comp_id,
      ← Category.id_comp (cokernel.π ι), ← Preadditive.nsmul_comp,
      ← kernel.lift_ι (p • 𝟙 G) _ h0, Category.assoc]
    exact (congrArg _ (cokernel.condition ι)).trans comp_zero

/-- **Filtered colimits.** For quasi-compact quasi-separated `X` and `Y`, if the comparison
maps along `f` are bijective for every member of a filtered diagram of abelian sheaves on `Y`,
they are bijective for its colimit: étale cohomology of a qcqs scheme commutes with filtered
colimits, and so does `f^*`. -/
theorem bijective_cohomologyMap_of_isColimit [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) (h : ∀ j, Function.Bijective (cohomologyMap f (D.obj j) q)) :
    Function.Bijective (cohomologyMap f c.pt q) := by
  have : PreservesColimitsOfSize.{u, u} ((f)^*[AddCommGrpCat.{u + 1}]) :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).leftAdjoint_preservesColimits
  have hc' := isColimitOfPreserves ((f)^*[AddCommGrpCat.{u + 1}]) hc
  have HY := Scheme.H_map_isColimit_of_isFiltered Y hc q
  have HX := Scheme.H_map_isColimit_of_isFiltered X hc' q
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, x', rfl⟩ := HY.1 x
    obtain ⟨j', φ, hφ⟩ := HX.2 j _ ((cohomologyMap_map f q (c.ι.app j) x').symm.trans hx)
    have : Sheaf.H.map (D.map φ) q x' = 0 := (h j').1 (by
      rw [cohomologyMap_map, map_zero]
      exact hφ)
    rw [← c.w φ, Sheaf.H.map_comp_apply, this, map_zero]
  · obtain ⟨j, y', rfl⟩ := HX.1 y
    obtain ⟨x', rfl⟩ := (h j).2 y'
    exact ⟨Sheaf.H.map (c.ι.app j) q x', cohomologyMap_map f q _ x'⟩

/-- A torsion abelian sheaf on the small étale site is the colimit of a filtered diagram,
indexed by a small category in universe `u`, of sheaves each killed by a positive integer:
the chain of its subsheaves `G[k!]`. -/
theorem _root_.CategoryTheory.Sheaf.IsTorsion.exists_isColimit_nsmul_eq_zero
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    ∃ (D : AsSmall.{u} ℕ ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (c : Cocone D)
      (_ : IsColimit c), c.pt = G ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ n • 𝟙 (D.obj j) = 0 := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : AB5OfSize.{0, 0} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have hN : Monotone fun k : ℕ ↦ kernelSubobject (k.factorial • 𝟙 G) := fun k k' hk ↦ by
    obtain ⟨r, hr⟩ := Nat.factorial_dvd_factorial hk
    have : k'.factorial • 𝟙 G = (k.factorial • 𝟙 G) ≫ (r • 𝟙 G) := by
      simp only [hr, Preadditive.comp_nsmul, Category.comp_id, mul_comm, mul_nsmul]
      exact smul_comm _ _ _
    change kernelSubobject _ ≤ kernelSubobject _
    rw [this]
    exact kernelSubobject_comp_le _ _
  let K : ℕ ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    hN.functor ⋙ Subobject.underlying
  let α : K ⟶ (Functor.const ℕ).obj G :=
    { app k := (kernelSubobject (k.factorial • 𝟙 G)).arrow
      naturality k k' f := by simp [K] }
  have : ∀ k, Mono (α.app k) := fun k ↦ inferInstanceAs (Mono (Subobject.arrow _))
  have : Mono α := NatTrans.mono_of_mono_app α
  let cK : Cocone K := { pt := G, ι := α }
  let t := colimit.desc K cK
  have ht : Mono t := colim.map_mono' α (colimit.isColimit K) (isColimitConstCocone ℕ G) t
    (fun k ↦ (colimit.ι_desc _ _).trans (Category.comp_id _).symm)
  have hG' := (Scheme.isTorsion_iff_isAddTorsion_sheafFiber G).1 hG
  have : Epi t := by
    refine ⟨fun {G'} g h hgh ↦ ?_⟩
    have hk (k : ℕ) : α.app k ≫ g = α.app k ≫ h := by
      simpa [t, cK] using colimit.ι K k ≫= hgh
    have : HasLimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have : AB5OfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} := inferInstance
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    refine sheafHom_ext_of_sheafFiber_map_algClosurePoint fun p ↦ ?_
    have := (pointSmallEtale (Y.algClosurePoint p)).sheafFiber_additive
      (A := AddCommGrpCat.{u + 1})
    ext x
    obtain ⟨m, hm, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hG' _ _ x)
    have : LocallySmall.{u} Y.Etale := ⟨fun _ _ ↦ small_self _⟩
    have : PreservesFiniteLimits
        ((pointSmallEtale (Y.algClosurePoint p)).sheafFiber (A := AddCommGrpCat.{u + 1})) :=
      inferInstance
    have hS :=
      (ShortComplex.kernelSequence_exact (m.factorial • 𝟙 G)).map_of_mono_of_preservesKernel
        (pointSmallEtale (Y.algClosurePoint p)).sheafFiber inferInstance inferInstance
    have hx' : (pointSmallEtale (Y.algClosurePoint p)).sheafFiber.map (m.factorial • 𝟙 G) x =
        0 := by
      obtain ⟨r, hr⟩ := Nat.dvd_factorial hm le_rfl
      simp [hr, mul_nsmul, hx]
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hS x hx'
    have e : kernel.ι (m.factorial • 𝟙 G) ≫ g = kernel.ι (m.factorial • 𝟙 G) ≫ h := by
      rw [← kernelSubobject_arrow', Category.assoc, Category.assoc]
      exact (kernelSubobjectIso _).inv ≫= hk m
    have := congr((pointSmallEtale (Y.algClosurePoint p)).sheafFiber.map $e y)
    simp only [Functor.map_comp] at this
    rw [← hy]
    exact this
  have : IsIso ((colimit.isColimit K).desc cK) := isIso_of_mono_of_epi t
  have hcK : IsColimit cK := IsColimit.ofPointIso (colimit.isColimit K)
  refine ⟨AsSmall.equiv.inverse ⋙ K, cK.whisker AsSmall.equiv.inverse,
    IsColimit.whiskerEquivalence hcK AsSmall.equiv.symm, rfl, fun k ↦
      ⟨(ULift.down k).factorial, (ULift.down k).factorial_pos, ?_⟩⟩
  have := kernelSubobject_arrow_comp ((ULift.down k).factorial • 𝟙 G)
  rw [Preadditive.comp_nsmul, Category.comp_id] at this
  change (ULift.down k).factorial • 𝟙 (K.obj (ULift.down k)) = 0
  rw [← cancel_mono (α.app (ULift.down k)), Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  exact this

/-- **Torsion sheaves.** For quasi-compact quasi-separated `X` and `Y`, if the comparison maps
along `f` are bijective in every degree for every abelian sheaf killed by a prime, they are
bijective for every torsion abelian sheaf. -/
theorem bijective_cohomologyMap_of_isTorsion [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hp : ∀ (p : ℕ) (_ : p.Prime) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}),
      p • 𝟙 G = 0 → ∀ q, Function.Bijective (cohomologyMap f G q))
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) (q : ℕ) :
    Function.Bijective (cohomologyMap f G q) := by
  obtain ⟨D, c, hc, rfl, hD⟩ := hG.exists_isColimit_nsmul_eq_zero
  refine bijective_cohomologyMap_of_isColimit f hc q fun j ↦ ?_
  obtain ⟨n, hn, hnD⟩ := hD j
  exact bijective_cohomologyMap_of_nsmul_eq_zero f hp n hn _ hnD q

end AlgebraicGeometry.Etale
