/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Extensive
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.WeilSheaf.UpperStarId

/-!
# Artin–Schreier sheaves and the Fourier–Deligne transform

Let `k₀` be a finite field with `q` elements and `ψ` an additive character of `k₀` with values
in `ℚ̄_ℓ`. The Artin–Schreier map `AS : 𝔸¹ ⟶ 𝔸¹`, `x ↦ x^q - x`, is a finite étale torsor
under `k₀`, acting by the translations `σ_c : x ↦ x + c`; it is defined over `k₀`, so the
pushforward `AS_* ℚ̄_ℓ` of the constant Weil sheaf is a Weil sheaf, and each `σ_c`, satisfying
`σ_c ≫ AS = AS`, acts on it by a morphism of Weil sheaves
(`AlgebraicGeometry.WeilSheaf.artinSchreierTranslationAction`). The *Artin–Schreier sheaf*
`ℒ_ψ` is the image of the idempotent `e_ψ = q⁻¹ ∑_{c ∈ k₀} ψ(-c) σ_c` of `AS_* ℚ̄_ℓ`, its
`ψ`-isotypic component, and `ℒ_{ψ(a x)}` is its pullback along `x ↦ a x`
(`AlgebraicGeometry.artinSchreier`). It is lisse of rank one and pure of weight zero.

For a finite index type `ι` of cardinality `r`, the *Fourier–Deligne transform* of a Weil
complex `K` on the affine space `𝔸^ι = 𝔸(ι; Spec k₀)` is

`FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ)[r]`,

where `pr₁, pr₂ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι` are the projections and
`⟨-, -⟩ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸¹`, `(x, y) ↦ ∑ᵢ xᵢ yᵢ`, is the standard pairing
(`AlgebraicGeometry.affineSpaceFourierTransform`), with Laumon's shift by the relative dimension
`r`. The tensor product with the lisse kernel `⟨-, -⟩^* ℒ_ψ` is the internal hom out of its
dual, derived on the category of pro-étale Weil sheaves
(`AlgebraicGeometry.WeilComplex.ihomLisse`). Since `affineLine k₀` is `𝔸(PUnit; Spec k₀)`, the
transform on the affine line, `FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]` with `μ` the
multiplication (`AlgebraicGeometry.fourierTransform`), is the case `ι = PUnit`: there the pairing
is the multiplication (`AlgebraicGeometry.affineSpacePair.pairing_punit`).

## Main declarations

- `AlgebraicGeometry.WeilSheaf.artinSchreierPushforward`: `AS_* ℚ̄_ℓ`, with the translation
  action `AlgebraicGeometry.WeilSheaf.artinSchreierTranslationAction`.
- `AlgebraicGeometry.artinSchreier`: the Artin–Schreier sheaves.
- `AlgebraicGeometry.affineSpacePair`: `𝔸^ι ×_{k₀} 𝔸^ι`, with its projections
  `AlgebraicGeometry.affineSpacePair.fst`, `AlgebraicGeometry.affineSpacePair.snd` and the
  pairing `AlgebraicGeometry.affineSpacePair.pairing`.
- `AlgebraicGeometry.affineSpaceFourierKernel` and
  `AlgebraicGeometry.affineSpaceFourierTransform`: the kernel `⟨-, -⟩^* ℒ_ψ` and the
  Fourier–Deligne transform on `𝔸^ι`.
- `AlgebraicGeometry.fourierKernel` and `AlgebraicGeometry.fourierTransform`: their cases
  `ι = PUnit`, the kernel and the Fourier–Deligne transform of the affine line.
- `AlgebraicGeometry.WeilSheaf.HasLinearArtinSchreierConstituent`: a geometric linear
  Artin–Schreier sheaf is a constituent of the geometric restriction of a Weil sheaf.

## Implementation notes

The compatibility of the translation action with the Weil structure of `AS_* ℚ̄_ℓ` is the
general `AlgebraicGeometry.ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange`, the
translations commuting with the geometric Frobenius.

That `ℒ_ψ` is lisse (`AlgebraicGeometry.WeilSheaf.isLisse_image_artinSchreierIdempotent`) is
checked on the pro-étale cover `ĀS` itself. The geometric Artin–Schreier map is a `k₀`-torsor
(`AlgebraicGeometry.affineLine.isIso_sigmaDesc_lift_geometricTranslation`), so for
`v : V ⟶ 𝔸¹_{k̄}` the fibre product `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` is a disjoint union of `#k₀` copies
of `V`. The sections of `ĀS^* ĀS_* ℚ̄_ℓ` over `V` are the locally finite functions on it, and
there the projector `e_ψ` factors as an averaging map to the sections of `ℚ̄_ℓ` followed by a
splitting map. Both are `ℚ̄_ℓ,X`-linear: the evaluations along the sections of the torsor are
morphisms of sheaves of modules (`AlgebraicGeometry.affineLine.artinSchreierEvalHom`, the
pullback of a translation followed by the counit of `ĀS^* ⊣ ĀS_*`), averaging is a linear
combination of them, and they are jointly injective, while splitting followed by each of them is
a scalar. This split epi–mono factorisation identifies the image of `e_ψ` with `ℚ̄_ℓ` as a sheaf
of `ℚ̄_ℓ,X`-modules.

The constructibility statement which makes the tensor product with a lisse sheaf land in Weil
complexes is reduced by dévissage to the case of a single Weil sheaf, stated with `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor MonoidalCategory Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀] [Finite k₀]

/-- The Artin–Schreier map `AS : x ↦ x^q - x` of the affine line over `k₀`, `q = #k₀`, the Lang
isogeny of the additive group. -/
noncomputable def affineLine.artinSchreierMap : affineLine k₀ ⟶ affineLine k₀ :=
  letI := Fintype.ofFinite k₀
  AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k₀)) (Fintype.card k₀)

instance : (affineLine.artinSchreierMap k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.artinSchreierMap_over _ _ _⟩

instance : IsFinite (affineLine.artinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.isFinite_artinSchreierMap _ _ Fintype.one_lt_card.ne'

/-- The translation `σ_c : x ↦ x + c` of the affine line over `k₀` by `c ∈ k₀`. -/
noncomputable def affineLine.translation (c : k₀) : affineLine k₀ ⟶ affineLine k₀ :=
  AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom c

instance (c : k₀) : (affineLine.translation k₀ c).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.translation_over _⟩

omit [Finite k₀] in
lemma affineLine.translation_add (c d : k₀) :
    affineLine.translation k₀ (c + d) =
      affineLine.translation k₀ c ≫ affineLine.translation k₀ d := by
  simp only [affineLine.translation, map_add]
  exact AffineSpace.translation_add _ _

omit [Finite k₀] in
lemma affineLine.translation_zero : affineLine.translation k₀ 0 = 𝟙 _ := by
  simp only [affineLine.translation, map_zero]
  exact AffineSpace.translation_zero

omit [Finite k₀] in
@[reassoc]
lemma affineLine.translation_comp_translation_neg (c : k₀) :
    affineLine.translation k₀ c ≫ affineLine.translation k₀ (-c) = 𝟙 _ := by
  rw [← affineLine.translation_add, add_neg_cancel, affineLine.translation_zero]

omit [Finite k₀] in
@[reassoc]
lemma affineLine.translation_neg_comp_translation (c : k₀) :
    affineLine.translation k₀ (-c) ≫ affineLine.translation k₀ c = 𝟙 _ := by
  rw [← affineLine.translation_add, neg_add_cancel, affineLine.translation_zero]

@[reassoc]
lemma affineLine.translation_comp_artinSchreierMap (c : k₀) :
    affineLine.translation k₀ c ≫ affineLine.artinSchreierMap k₀ =
      affineLine.artinSchreierMap k₀ := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.translation_comp_artinSchreierMap_of_finiteField k₀ _ fun _ ↦ c

/-- The multiplication `x ↦ a x` of the affine line over `k₀` by `a ∈ k₀`. -/
noncomputable def affineLine.smul (a : k₀) : affineLine k₀ ⟶ affineLine k₀ :=
  AffineSpace.smul PUnit (Spec (CommRingCat.of k₀)) ((Scheme.ΓSpecIso (.of k₀)).inv.hom a)

instance (a : k₀) : (affineLine.smul k₀ a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.smul_over _ _ _⟩

/-- The translation `σ_c` of the geometric affine line `𝔸¹_{k̄}`, the base change of the
translation of `𝔸¹_{k₀}`, as an automorphism. -/
noncomputable def affineLine.geometricTranslationIso (c : k₀) :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber where
  hom := Scheme.Hom.geometricFiberMap (affineLine.translation k₀ c)
    (comp_over (affineLine.translation k₀ c) (Spec (CommRingCat.of k₀)))
  inv := Scheme.Hom.geometricFiberMap (affineLine.translation k₀ (-c))
    (comp_over (affineLine.translation k₀ (-c)) (Spec (CommRingCat.of k₀)))
  hom_inv_id := Scheme.Hom.geometricFiber_hom_ext _
    (by rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc,
      affineLine.translation_comp_translation_neg, Category.comp_id, Category.id_comp])
    (by simp)
  inv_hom_id := Scheme.Hom.geometricFiber_hom_ext _
    (by rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc,
      affineLine.translation_neg_comp_translation, Category.comp_id, Category.id_comp])
    (by simp)

/-- The base change `ĀS : 𝔸¹_{k̄} ⟶ 𝔸¹_{k̄}` of the Artin–Schreier map to `k̄`. -/
noncomputable abbrev affineLine.geometricArtinSchreierMap :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Scheme.Hom.geometricFiberMap (affineLine.artinSchreierMap k₀)
    (comp_over (affineLine.artinSchreierMap k₀) (Spec (CommRingCat.of k₀)))

/-- The base change of `σ_c ≫ AS = AS` to `k̄`. -/
lemma affineLine.geometricTranslation_comp_artinSchreierMap (c : k₀) :
    (affineLine.geometricTranslationIso k₀ c).hom ≫ affineLine.geometricArtinSchreierMap k₀ =
      affineLine.geometricArtinSchreierMap k₀ :=
  Scheme.Hom.geometricFiber_hom_ext _
    (by rw [affineLine.geometricTranslationIso, affineLine.geometricArtinSchreierMap,
      Category.assoc,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc,
      affineLine.translation_comp_artinSchreierMap])
    (by simp [affineLine.geometricTranslationIso, affineLine.geometricArtinSchreierMap])

/-- The translations of the geometric affine line commute with its geometric Frobenius: they
are base changes of translations defined over `k₀`. -/
lemma affineLine.geometricTranslation_comp_geometricGaloisFrobenius (c : k₀) :
    (affineLine.geometricTranslationIso k₀ c).hom ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≫
        (affineLine.geometricTranslationIso k₀ c).hom :=
  Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius _ (comp_over _ _)

omit [Finite k₀] in
/-- The geometric translations compose: `σ̄_c ≫ σ̄_d = σ̄_{c + d}`. -/
@[reassoc]
lemma affineLine.geometricTranslationIso_hom_comp (c d : k₀) :
    (affineLine.geometricTranslationIso k₀ c).hom ≫ (affineLine.geometricTranslationIso k₀ d).hom =
      (affineLine.geometricTranslationIso k₀ (c + d)).hom := by
  simp only [affineLine.geometricTranslationIso]
  rw [← Scheme.Hom.geometricFiberMap_comp]
  congr 1
  exact (affineLine.translation_add k₀ c d).symm

/-- The Artin–Schreier map of the affine line over `k₀` is a `k₀`-torsor: the map
`∐_{c ∈ k₀} 𝔸¹ ⟶ 𝔸¹ ×_{AS} 𝔸¹`, `(𝟙, σ_c)` on the summand indexed by `c`, is an isomorphism
(`AlgebraicGeometry.AffineSpace.isIso_artinSchreierTorsorMap`). -/
lemma affineLine.isIso_sigmaDesc_lift_translation :
    IsIso (Sigma.desc fun c : k₀ ↦ pullback.lift (f := affineLine.artinSchreierMap k₀)
      (g := affineLine.artinSchreierMap k₀) (𝟙 _) (affineLine.translation k₀ c)
      (by rw [Category.id_comp, affineLine.translation_comp_artinSchreierMap]) :
      ∐ (fun _ : k₀ ↦ affineLine k₀) ⟶ _) := by
  let := Fintype.ofFinite k₀
  have := AffineSpace.isIso_artinSchreierTorsorMap (n := PUnit.{u + 1})
    (S := Spec (CommRingCat.of k₀)) k₀ (Scheme.ΓSpecIso (.of k₀)).inv.hom
  let ε : (PUnit.{u + 1} → k₀) ≃ k₀ := Equiv.funUnique _ _
  have h : (Sigma.desc fun c : k₀ ↦ pullback.lift (f := affineLine.artinSchreierMap k₀)
      (g := affineLine.artinSchreierMap k₀) (𝟙 _) (affineLine.translation k₀ c)
      (by rw [Category.id_comp, affineLine.translation_comp_artinSchreierMap])) =
      (Sigma.reindex ε fun _ : k₀ ↦ affineLine k₀).inv ≫
        AffineSpace.artinSchreierTorsorMap (n := PUnit.{u + 1}) k₀
          (Scheme.ΓSpecIso (.of k₀)).inv.hom := by
    refine Sigma.hom_ext _ _ fun c ↦ ?_
    obtain ⟨a, rfl⟩ := ε.surjective c
    rw [colimit.ι_desc, Sigma.ι_reindex_inv_assoc]
    simp only [Cofan.mk_ι_app, AffineSpace.artinSchreierTorsorMap]
    erw [colimit.ι_desc]
    rfl
  rw [h]
  infer_instance

/-- The geometric Artin–Schreier map `ĀS` of `𝔸¹_{k̄}` is a `k₀`-torsor: the map
`∐_{c ∈ k₀} 𝔸¹_{k̄} ⟶ 𝔸¹_{k̄} ×_{ĀS} 𝔸¹_{k̄}`, `(𝟙, σ̄_c)` on the summand indexed by `c`, is an
isomorphism. It is the base change of
`AlgebraicGeometry.affineLine.isIso_sigmaDesc_lift_translation` along `𝔸¹_{k̄} ⟶ 𝔸¹`
(`CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_lift_comp`), the square formed by `ĀS` and
`AS` being cartesian. -/
lemma affineLine.isIso_sigmaDesc_lift_geometricTranslation :
    IsIso (Sigma.desc fun c : k₀ ↦ pullback.lift
      (f := affineLine.geometricArtinSchreierMap k₀) (g := affineLine.geometricArtinSchreierMap k₀)
      (𝟙 _) (affineLine.geometricTranslationIso k₀ c).hom
      (by rw [Category.id_comp, affineLine.geometricTranslation_comp_artinSchreierMap]) :
      ∐ (fun _ : k₀ ↦ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶ _) := by
  have := affineLine.isIso_sigmaDesc_lift_translation k₀
  set p := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  have h₁ := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp (affineLine.artinSchreierMap k₀)
    (affineLine.translation k₀) (affineLine.translation_comp_artinSchreierMap k₀) p
  have hsq : affineLine.geometricArtinSchreierMap k₀ ≫ p = p ≫ affineLine.artinSchreierMap k₀ :=
    Scheme.Hom.geometricFiberMap_comp_geometricFiberProj _ _
  have hP : IsPullback (pullback.fst (affineLine.geometricArtinSchreierMap k₀)
      (affineLine.geometricArtinSchreierMap k₀))
      (pullback.snd (affineLine.geometricArtinSchreierMap k₀)
        (affineLine.geometricArtinSchreierMap k₀) ≫ p)
      (p ≫ affineLine.artinSchreierMap k₀) (affineLine.artinSchreierMap k₀) := by
    have := (IsPullback.of_hasPullback (affineLine.geometricArtinSchreierMap k₀)
      (affineLine.geometricArtinSchreierMap k₀)).flip.paste_horiz
      (Scheme.Hom.isPullback_geometricFiberMap (affineLine.artinSchreierMap k₀)
        (comp_over (affineLine.artinSchreierMap k₀) (Spec (CommRingCat.of k₀)))).flip
    rw [hsq] at this
    exact this.flip
  suffices IsIso (Sigma.desc (fun c : k₀ ↦ pullback.lift
      (f := affineLine.geometricArtinSchreierMap k₀) (g := affineLine.geometricArtinSchreierMap k₀)
      (𝟙 _) (affineLine.geometricTranslationIso k₀ c).hom
      (by rw [Category.id_comp, affineLine.geometricTranslation_comp_artinSchreierMap])) ≫
        hP.isoPullback.hom) from IsIso.of_isIso_comp_right _ hP.isoPullback.hom
  convert h₁ using 1
  refine Sigma.hom_ext _ _ fun c ↦ ?_
  simp only [colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply pullback.hom_ext
  · simp
  · simp [affineLine.geometricTranslationIso, p]

/-- The geometric Artin–Schreier map is étale, as a base change of `AS`. -/
instance affineLine.etale_geometricArtinSchreierMap :
    Etale (affineLine.geometricArtinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  refine Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale) _ _ ?_
  exact AffineSpace.etale_artinSchreierMap PUnit _ (by
    rw [← map_natCast (Scheme.ΓSpecIso (.of k₀)).inv.hom, FiniteField.cast_card_eq_zero,
      map_zero])

/-- The geometric Artin–Schreier map is surjective, as a base change of `AS`
(`AlgebraicGeometry.AffineSpace.surjective_artinSchreierMap`). -/
instance affineLine.surjective_geometricArtinSchreierMap :
    Surjective (affineLine.geometricArtinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Surjective) _ _
    ⟨AffineSpace.surjective_artinSchreierMap k₀⟩

end AffineLine

section ArtinSchreierTorsor

/-! ### The trivialisation of `ĀS^* ĀS_* ℚ̄_ℓ`

Pulled back along itself, the geometric Artin–Schreier map `ĀS` becomes trivial: for
`v : V ⟶ 𝔸¹_{k̄}` the sections `x ↦ (x, σ̄_c (v x))`, `c ∈ k₀`, decompose
`V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` (taken along `v ≫ ĀS` and `ĀS`) into `#k₀` copies of `V`. The sections of
`ĀS^* ĀS_* ℚ̄_ℓ` over `V` are the locally finite functions on this fibre product, and the
projector `e_ψ = q⁻¹ ∑_c ψ(-c) σ_c` factors as the averaging map
`h ↦ (x ↦ q⁻¹ ∑_c ψ(-c) h(x, σ̄_c (v x)))` to the sections of `ℚ̄_ℓ` followed by the splitting
map `g ↦ ((x, σ̄_c (v x)) ↦ ψ(c) g(x))`, whose composite the other way round is the identity.
-/

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

variable {V : Scheme.{u}} (v : V ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The section `x ↦ (x, σ̄_c (v x))` of the first projection `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄} ⟶ V`, the
fibre product taken along `v ≫ ĀS` and `ĀS`. -/
noncomputable def affineLine.artinSchreierSection (c : k₀) : V ⟶ pullback (v ≫ ĀS) ĀS :=
  pullback.lift (𝟙 V) (v ≫ (affineLine.geometricTranslationIso k₀ c).hom)
    (by simp [affineLine.geometricTranslation_comp_artinSchreierMap])

@[reassoc (attr := simp)]
lemma affineLine.artinSchreierSection_fst (c : k₀) :
    affineLine.artinSchreierSection v c ≫ pullback.fst _ _ = 𝟙 V :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma affineLine.artinSchreierSection_snd (c : k₀) :
    affineLine.artinSchreierSection v c ≫ pullback.snd _ _ =
      v ≫ (affineLine.geometricTranslationIso k₀ c).hom :=
  pullback.lift_snd _ _ _

@[simp]
lemma affineLine.artinSchreierSection_fst_apply (c : k₀) (x : V) :
    pullback.fst (v ≫ ĀS) ĀS (affineLine.artinSchreierSection v c x) = x := by
  rw [← Scheme.Hom.comp_apply, affineLine.artinSchreierSection_fst]
  rfl

/-- The sections `x ↦ (x, σ̄_c (v x))` decompose `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` into a disjoint union of
copies of `V`, the geometric Artin–Schreier map being a `k₀`-torsor
(`AlgebraicGeometry.affineLine.isIso_sigmaDesc_lift_geometricTranslation`). -/
instance affineLine.isIso_sigmaDesc_artinSchreierSection :
    IsIso (Sigma.desc (affineLine.artinSchreierSection v) : ∐ (fun _ : k₀ ↦ V) ⟶ _) := by
  have := affineLine.isIso_sigmaDesc_lift_geometricTranslation k₀
  exact FinitaryPreExtensive.isIso_sigmaDesc_lift_comp _ _
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀) v

/-- The homeomorphism `Σ_{c ∈ k₀} V ≃ V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}`, `(c, x) ↦ (x, σ̄_c (v x))`. -/
noncomputable def affineLine.artinSchreierHomeomorph :
    (Σ _ : k₀, V) ≃ₜ (pullback (v ≫ ĀS) ĀS : Scheme.{u}) :=
  (sigmaMk fun _ : k₀ ↦ V).trans (Sigma.desc (affineLine.artinSchreierSection v)).homeomorph

lemma affineLine.artinSchreierHomeomorph_apply (c : k₀) (x : V) :
    affineLine.artinSchreierHomeomorph v ⟨c, x⟩ = affineLine.artinSchreierSection v c x := by
  simp only [affineLine.artinSchreierHomeomorph, Homeomorph.trans_apply, sigmaMk_mk,
    Scheme.Hom.homeomorph_apply, ← Scheme.Hom.comp_apply, colimit.ι_desc, Cofan.mk_ι_app]

/-- The index `c` of the summand `x ↦ (x, σ̄_c (v x))` of `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` containing a
point. -/
noncomputable def affineLine.artinSchreierIndex (z : (pullback (v ≫ ĀS) ĀS : Scheme.{u})) : k₀ :=
  ((affineLine.artinSchreierHomeomorph v).symm z).1

@[simp]
lemma affineLine.artinSchreierIndex_artinSchreierSection (c : k₀) (x : V) :
    affineLine.artinSchreierIndex v (affineLine.artinSchreierSection v c x) = c := by
  rw [affineLine.artinSchreierIndex, ← affineLine.artinSchreierHomeomorph_apply,
    Homeomorph.symm_apply_apply]

/-- Every point of `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` is `(x, σ̄_c (v x))` for `c` its index and `x` its first
projection. -/
lemma affineLine.artinSchreierSection_artinSchreierIndex
    (z : (pullback (v ≫ ĀS) ĀS : Scheme.{u})) :
    affineLine.artinSchreierSection v (affineLine.artinSchreierIndex v z)
      (pullback.fst (v ≫ ĀS) ĀS z) = z := by
  obtain ⟨⟨c, x⟩, rfl⟩ := (affineLine.artinSchreierHomeomorph v).surjective z
  rw [affineLine.artinSchreierHomeomorph_apply, affineLine.artinSchreierIndex_artinSchreierSection,
    affineLine.artinSchreierSection_fst_apply]

lemma affineLine.isLocallyConstant_artinSchreierIndex :
    IsLocallyConstant (affineLine.artinSchreierIndex v) := by
  refine IsLocallyConstant.comp_continuous ?_ (affineLine.artinSchreierHomeomorph v).symm.continuous
  refine IsLocallyConstant.iff_isOpen_fiber.2 fun c ↦ ?_
  convert isOpen_range_sigmaMk (σ := fun _ : k₀ ↦ V) (i := c)
  ext ⟨d, x⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro rfl
    exact ⟨x, rfl⟩
  · rintro ⟨y, hy⟩
    exact (congrArg Sigma.fst hy).symm

variable {v} in
/-- The sections `x ↦ (x, σ̄_c (v x))` are natural in `v`. -/
@[reassoc]
lemma affineLine.artinSchreierSection_comp_pullbackMap {V' : Scheme.{u}}
    (v' : V' ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (φ : V' ⟶ V)
    (hφ : φ ≫ v = v') (c : k₀) :
    affineLine.artinSchreierSection v' c ≫ pullback.map (v' ≫ ĀS) ĀS (v ≫ ĀS) ĀS φ (𝟙 _) (𝟙 _)
      (by simp [← hφ]) (by simp) = φ ≫ affineLine.artinSchreierSection v c := by
  apply pullback.hom_ext <;> simp [← hφ]

variable {v} in
/-- The index of a point is natural in `v`. -/
lemma affineLine.artinSchreierIndex_pullbackMap {V' : Scheme.{u}}
    (v' : V' ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (φ : V' ⟶ V)
    (hφ : φ ≫ v = v') (z : (pullback (v' ≫ ĀS) ĀS : Scheme.{u})) :
    affineLine.artinSchreierIndex v (pullback.map (v' ≫ ĀS) ĀS (v ≫ ĀS) ĀS φ (𝟙 _) (𝟙 _)
      (by simp [← hφ]) (by simp) z) = affineLine.artinSchreierIndex v' z := by
  rw [← affineLine.artinSchreierSection_artinSchreierIndex v' z, ← Scheme.Hom.comp_apply,
    affineLine.artinSchreierSection_comp_pullbackMap v' φ hφ, Scheme.Hom.comp_apply,
    affineLine.artinSchreierIndex_artinSchreierSection,
    affineLine.artinSchreierIndex_artinSchreierSection]

/-- The translation `(x, y) ↦ (x, σ̄_c y)` of `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` carries the summand indexed by
`d` to the summand indexed by `d + c`. -/
@[reassoc]
lemma affineLine.artinSchreierSection_comp_pullbackMap_translation (c d : k₀) :
    affineLine.artinSchreierSection v d ≫ pullback.map (v ≫ ĀS) ĀS (v ≫ ĀS) ĀS (𝟙 _)
      (affineLine.geometricTranslationIso k₀ c).hom (𝟙 _) (by simp)
      (by simp [affineLine.geometricTranslation_comp_artinSchreierMap]) =
      affineLine.artinSchreierSection v (d + c) := by
  apply pullback.hom_ext
  · simp
  · simp [affineLine.geometricTranslationIso_hom_comp]

open PadicAlgCl in
variable (l) in
/-- The `ℚ̄_ℓ`-linear map `g ↦ ((x, σ̄_c (v x)) ↦ ψ(c) g(x))` from locally finite functions on `V`
to locally finite functions on `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}`. -/
noncomputable def affineLine.artinSchreierSplit (ψ : AddChar k₀ (PadicAlgCl l)) :
    locallyFiniteFunctions l V →ₗ[PadicAlgCl l]
      locallyFiniteFunctions l (pullback (v ≫ ĀS) ĀS : Scheme.{u}) where
  toFun g := ⟨⟨fun z ↦ ψ (affineLine.artinSchreierIndex v z) * g.1 (pullback.fst (v ≫ ĀS) ĀS z),
    ((affineLine.isLocallyConstant_artinSchreierIndex v).comp ψ).continuous.mul
      (g.1.continuous.comp (pullback.fst (v ≫ ĀS) ĀS).continuous)⟩, fun z ↦ by
    obtain ⟨U, hU, hfin⟩ := g.2 (pullback.fst (v ≫ ĀS) ĀS z)
    refine ⟨(pullback.fst (v ≫ ĀS) ĀS).base ⁻¹' U ∩ affineLine.artinSchreierIndex v ⁻¹'
        {affineLine.artinSchreierIndex v z},
      Filter.inter_mem ((pullback.fst (v ≫ ĀS) ĀS).continuous.continuousAt.preimage_mem_nhds hU)
        (((affineLine.isLocallyConstant_artinSchreierIndex v).isOpen_fiber _).mem_nhds rfl),
      Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℚ_[l] (g.1 '' U)).map
        (LinearMap.mulLeft ℚ_[l] (ψ (affineLine.artinSchreierIndex v z)))) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, ⟨hy, hy'⟩, rfl⟩
    refine ⟨g.1 (pullback.fst (v ≫ ĀS) ĀS y), Submodule.subset_span ⟨_, hy, rfl⟩, ?_⟩
    have hy'' : affineLine.artinSchreierIndex v y = affineLine.artinSchreierIndex v z := hy'
    simp [hy'']⟩
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ ↦ mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (ContinuousMap.ext fun _ ↦ mul_left_comm _ _ _)

@[simp]
lemma affineLine.artinSchreierSplit_apply (ψ : AddChar k₀ (PadicAlgCl l))
    (g : PadicAlgCl.locallyFiniteFunctions l V) (z) :
    (affineLine.artinSchreierSplit l v ψ g).1 z =
      ψ (affineLine.artinSchreierIndex v z) * g.1 (pullback.fst (v ≫ ĀS) ĀS z) :=
  rfl

open PadicAlgCl in
variable (l) in
/-- The `ℚ̄_ℓ`-linear map `h ↦ (x ↦ q⁻¹ ∑_c ψ(-c) h(x, σ̄_c (v x)))` from locally finite functions
on `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` to locally finite functions on `V`. -/
noncomputable def affineLine.artinSchreierAverage (ψ : AddChar k₀ (PadicAlgCl l)) :
    locallyFiniteFunctions l (pullback (v ≫ ĀS) ĀS : Scheme.{u}) →ₗ[PadicAlgCl l]
      locallyFiniteFunctions l V :=
  letI := Fintype.ofFinite k₀
  ∑ c : k₀, ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) •
    locallyFiniteFunctionsComp l (affineLine.artinSchreierSection v c).base.hom

lemma affineLine.artinSchreierAverage_apply (ψ : AddChar k₀ (PadicAlgCl l))
    (h : PadicAlgCl.locallyFiniteFunctions l (pullback (v ≫ ĀS) ĀS : Scheme.{u})) (x : V) :
    letI := Fintype.ofFinite k₀
    (affineLine.artinSchreierAverage l v ψ h).1 x =
      ∑ c : k₀, ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) *
        h.1 (affineLine.artinSchreierSection v c x) := by
  simp [affineLine.artinSchreierAverage, LinearMap.sum_apply]

/-- Averaging after splitting is the identity: `q⁻¹ ∑_c ψ(-c) ψ(c) g = g`. -/
lemma affineLine.artinSchreierAverage_artinSchreierSplit (ψ : AddChar k₀ (PadicAlgCl l))
    (g : PadicAlgCl.locallyFiniteFunctions l V) :
    affineLine.artinSchreierAverage l v ψ (affineLine.artinSchreierSplit l v ψ g) = g := by
  let := Fintype.ofFinite k₀
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  rw [affineLine.artinSchreierAverage_apply]
  simp only [affineLine.artinSchreierSplit_apply,
    affineLine.artinSchreierIndex_artinSchreierSection,
    affineLine.artinSchreierSection_fst_apply]
  have hq : (Nat.card k₀ : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  calc ∑ c : k₀, (Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c) * (ψ c * g.1 x)
      = ∑ _c : k₀, (Nat.card k₀ : PadicAlgCl l)⁻¹ * g.1 x := Finset.sum_congr rfl fun c _ ↦ by
        rw [mul_assoc, ← mul_assoc (ψ (-c)), ← AddChar.map_add_eq_mul, neg_add_cancel,
          AddChar.map_zero_eq_one, one_mul]
    _ = g.1 x := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
          ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

/-- On functions on `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}`, the projector `q⁻¹ ∑_c ψ(-c) σ_c` is averaging
followed by splitting. -/
lemma affineLine.sum_apply_pullbackMap_translation (ψ : AddChar k₀ (PadicAlgCl l))
    (h : PadicAlgCl.locallyFiniteFunctions l (pullback (v ≫ ĀS) ĀS : Scheme.{u}))
    (z : (pullback (v ≫ ĀS) ĀS : Scheme.{u})) :
    letI := Fintype.ofFinite k₀
    ∑ c : k₀, ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) *
      h.1 (pullback.map (v ≫ ĀS) ĀS (v ≫ ĀS) ĀS (𝟙 _)
        (affineLine.geometricTranslationIso k₀ c).hom (𝟙 _) (by simp)
        (by simp [affineLine.geometricTranslation_comp_artinSchreierMap]) z) =
      (affineLine.artinSchreierSplit l v ψ (affineLine.artinSchreierAverage l v ψ h)).1 z := by
  let := Fintype.ofFinite k₀
  obtain ⟨⟨d, x⟩, rfl⟩ := (affineLine.artinSchreierHomeomorph v).surjective z
  rw [affineLine.artinSchreierHomeomorph_apply, affineLine.artinSchreierSplit_apply,
    affineLine.artinSchreierIndex_artinSchreierSection, affineLine.artinSchreierSection_fst_apply,
    affineLine.artinSchreierAverage_apply, Finset.mul_sum]
  simp_rw [← Scheme.Hom.comp_apply, affineLine.artinSchreierSection_comp_pullbackMap_translation]
  let G : k₀ → PadicAlgCl l := fun c ↦ (Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (d - c) *
    h.1 (affineLine.artinSchreierSection v c x)
  calc _ = ∑ c : k₀, G (Equiv.addLeft d c) := Finset.sum_congr rfl fun c _ ↦ by
          simp [G, sub_add_cancel_left]
    _ = ∑ c : k₀, G c := Equiv.sum_comp (Equiv.addLeft d) G
    _ = _ := Finset.sum_congr rfl fun c _ ↦ by
          simp only [G, sub_eq_add_neg, AddChar.map_add_eq_mul]
          ring

variable {v} in
lemma affineLine.artinSchreierSplit_comp {V' : Scheme.{u}}
    (v' : V' ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (φ : V' ⟶ V)
    (hφ : φ ≫ v = v') (ψ : AddChar k₀ (PadicAlgCl l))
    (g : PadicAlgCl.locallyFiniteFunctions l V) :
    affineLine.artinSchreierSplit l v' ψ (PadicAlgCl.locallyFiniteFunctionsComp l φ.base.hom g) =
      PadicAlgCl.locallyFiniteFunctionsComp l (pullback.map (v' ≫ ĀS) ĀS (v ≫ ĀS) ĀS φ (𝟙 _)
        (𝟙 _) (by simp [← hφ]) (by simp)).base.hom (affineLine.artinSchreierSplit l v ψ g) := by
  refine Subtype.ext (ContinuousMap.ext fun z ↦ ?_)
  simp only [affineLine.artinSchreierSplit_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
    ContinuousMap.comp_apply]
  rw [affineLine.artinSchreierIndex_pullbackMap v' φ hφ]
  congr 2
  change _ = (pullback.map (v' ≫ ĀS) ĀS (v ≫ ĀS) ĀS φ (𝟙 _) (𝟙 _) (by simp [← hφ]) (by simp) ≫
    pullback.fst (v ≫ ĀS) ĀS) z
  rw [pullback.lift_fst]
  rfl

variable {v} in
lemma affineLine.artinSchreierAverage_comp {V' : Scheme.{u}}
    (v' : V' ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (φ : V' ⟶ V)
    (hφ : φ ≫ v = v') (ψ : AddChar k₀ (PadicAlgCl l))
    (h : PadicAlgCl.locallyFiniteFunctions l (pullback (v ≫ ĀS) ĀS : Scheme.{u})) :
    affineLine.artinSchreierAverage l v' ψ (PadicAlgCl.locallyFiniteFunctionsComp l
      (pullback.map (v' ≫ ĀS) ĀS (v ≫ ĀS) ĀS φ (𝟙 _) (𝟙 _) (by simp [← hφ]) (by simp)).base.hom
        h) =
      PadicAlgCl.locallyFiniteFunctionsComp l φ.base.hom
        (affineLine.artinSchreierAverage l v ψ h) := by
  let := Fintype.ofFinite k₀
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  rw [affineLine.artinSchreierAverage_apply]
  simp only [PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply]
  rw [affineLine.artinSchreierAverage_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 2
  change (affineLine.artinSchreierSection v' c ≫ pullback.map (v' ≫ ĀS) ĀS (v ≫ ĀS) ĀS φ (𝟙 _)
    (𝟙 _) (by simp [← hφ]) (by simp)) x = (φ ≫ affineLine.artinSchreierSection v c) x
  rw [affineLine.artinSchreierSection_comp_pullbackMap v' φ hφ]

variable (l k₀) in
/-- The pullback `ĀS^* ĀS_* ℚ̄_ℓ`, computed by restriction along the weakly étale `ĀS`
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`): its sections over
`v : V ⟶ 𝔸¹_{k̄}` are the locally finite functions on `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}`. -/
noncomputable abbrev affineLine.artinSchreierPullbackPushforward :
    Sheaf (Scheme.ProEt.topology (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) :=
  (ProEtale.localizationRestriction (WeilCoefficients.{u} l) ĀS inferInstance).obj
    ((ĀS)_*[WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))

variable (l) in
/-- The morphism `ℚ̄_ℓ ⟶ ĀS^* ĀS_* ℚ̄_ℓ` given on sections over `v : V ⟶ 𝔸¹_{k̄}` by
`AlgebraicGeometry.affineLine.artinSchreierSplit`. -/
noncomputable def affineLine.artinSchreierSplitHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      affineLine.artinSchreierPullbackPushforward k₀ l :=
  ObjectProperty.homMk
    { app V := ModuleCat.ofHom (WeilCoefficients.uliftLinearMap
        (affineLine.artinSchreierSplit l V.unop.hom ψ))
      naturality V₁ V₂ φ := by
        ext ⟨g⟩
        exact congrArg ULift.up (affineLine.artinSchreierSplit_comp V₂.unop.hom φ.unop.left
          (φ.unop.w.trans (Category.comp_id _)) ψ g) }

variable (l) in
/-- The morphism `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` given on sections over `v : V ⟶ 𝔸¹_{k̄}` by
`AlgebraicGeometry.affineLine.artinSchreierAverage`. -/
noncomputable def affineLine.artinSchreierAverageHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    affineLine.artinSchreierPullbackPushforward k₀ l ⟶
      ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ObjectProperty.homMk
    { app V := ModuleCat.ofHom (WeilCoefficients.uliftLinearMap
        (affineLine.artinSchreierAverage l V.unop.hom ψ))
      naturality V₁ V₂ φ := by
        ext ⟨h⟩
        exact congrArg ULift.up (affineLine.artinSchreierAverage_comp V₂.unop.hom φ.unop.left
          (φ.unop.w.trans (Category.comp_id _)) ψ h) }

lemma affineLine.artinSchreierSplitHom_artinSchreierAverageHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    affineLine.artinSchreierSplitHom l ψ ≫ affineLine.artinSchreierAverageHom l ψ = 𝟙 _ := by
  ext V : 3
  ext ⟨g⟩
  exact congrArg ULift.up (affineLine.artinSchreierAverage_artinSchreierSplit V.unop.hom ψ g)

end ArtinSchreierTorsor

section AffineSpacePair

variable (ι : Type u) (k₀ : Type u) [Field k₀]

/-- The product `𝔸^ι ×_{k₀} 𝔸^ι` of the affine space `𝔸^ι = 𝔸(ι; Spec k₀)` with itself, with
its two projections and the standard pairing to the affine line. For `ι = PUnit` it is the
affine plane `AlgebraicGeometry.affinePlane`. -/
noncomputable def affineSpacePair : Scheme.{u} :=
  pullback (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))

noncomputable instance affineSpacePair.instOver :
    (affineSpacePair ι k₀).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.fst _ _ ≫ 𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)⟩

instance affineSpacePair.locallyOfFiniteType_over [Finite ι] :
    LocallyOfFiniteType (affineSpacePair ι k₀ ↘ Spec (CommRingCat.of k₀)) := by
  have : LocallyOfFiniteType
      (pullback.fst (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
        (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact inferInstanceAs (LocallyOfFiniteType (pullback.fst _ _ ≫ _))

/-- The first projection `pr₁ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι`. -/
noncomputable def affineSpacePair.fst : affineSpacePair ι k₀ ⟶ 𝔸(ι; Spec (CommRingCat.of k₀)) :=
  pullback.fst _ _

/-- The second projection `pr₂ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι`. -/
noncomputable def affineSpacePair.snd : affineSpacePair ι k₀ ⟶ 𝔸(ι; Spec (CommRingCat.of k₀)) :=
  pullback.snd _ _

instance affineSpacePair.isOver_fst :
    (affineSpacePair.fst ι k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance affineSpacePair.isOver_snd :
    (affineSpacePair.snd ι k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.condition.symm⟩

instance affineSpacePair.isSeparated_snd : IsSeparated (affineSpacePair.snd ι k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.quasiCompact_snd : QuasiCompact (affineSpacePair.snd ι k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.locallyOfFiniteType_snd [Finite ι] :
    LocallyOfFiniteType (affineSpacePair.snd ι k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The standard pairing `⟨-, -⟩ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸¹`, `(x, y) ↦ ∑ᵢ xᵢ yᵢ`, the morphism to
the affine line given by the global function `AlgebraicGeometry.AffineSpace.stdPairing`. -/
noncomputable def affineSpacePair.pairing [Fintype ι] : affineSpacePair ι k₀ ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (affineSpacePair ι k₀ ↘ Spec (CommRingCat.of k₀)) fun _ ↦
    AffineSpace.stdPairing ι (Spec (CommRingCat.of k₀))

instance affineSpacePair.isOver_pairing [Fintype ι] :
    (affineSpacePair.pairing ι k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

lemma affineSpacePair.pairing_appTop_coord [Fintype ι] :
    (affineSpacePair.pairing ι k₀).appTop (AffineSpace.coord _ PUnit.unit) =
      ∑ i : ι, (affineSpacePair.fst ι k₀).appTop (AffineSpace.coord _ i) *
        (affineSpacePair.snd ι k₀).appTop (AffineSpace.coord _ i) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

end AffineSpacePair

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

section Scalar

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ` commutes with the Weil structure of a Weil sheaf: the
Frobenius pullback, a pushforward, is `ℚ̄_ℓ`-linear. -/
lemma WeilSheaf.smul_comm_str (b : PadicAlgCl l) (F : WeilSheaf k₀ l X) :
    (WeilSheaf.frobeniusPullback k₀ l X).map
        (ProEtale.AdicSheaf.smul (ULift.up b) F.obj.carrier) ≫ F.obj.obj.str =
      F.obj.obj.str ≫ ProEtale.AdicSheaf.smul (ULift.up b) F.obj.carrier := by
  rw [ProEtale.AdicSheaf.adicLowerStar_map_smul, ProEtale.AdicSheaf.smul_comp]

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ`, as an endomorphism of a Weil sheaf. -/
noncomputable def WeilSheaf.smulEnd (b : PadicAlgCl l) (F : WeilSheaf k₀ l X) : F ⟶ F :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨ProEtale.AdicSheaf.smul (ULift.up b) F.obj.carrier, WeilSheaf.smul_comm_str b F⟩)

end Scalar

section ArtinSchreier

variable (k₀ l) in
/-- The pushforward `AS_* ℚ̄_ℓ` of the constant Weil sheaf along the Artin–Schreier map, a
Weil sheaf of rank `q` on the affine line. -/
noncomputable def WeilSheaf.artinSchreierPushforward : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.lowerStar (affineLine.artinSchreierMap k₀)).obj
    (WeilSheaf.adicConstant k₀ l (affineLine k₀))

variable (l) in
/-- The action of the translation `σ_c` on the underlying sheaf `ĀS_* ℚ̄_ℓ` of
`AS_* ℚ̄_ℓ`, pulling back sections along `σ_c` and using `σ_c ≫ AS = AS`:
```
ĀS_* ℚ̄_ℓ ⟶ ĀS_* σ̄_c* ℚ̄_ℓ ≅ (σ̄_c ≫ ĀS)_* ℚ̄_ℓ = ĀS_* ℚ̄_ℓ
```
-/
noncomputable def artinSchreierTranslationSheafHom (c : k₀) :
    (affineLine.geometricArtinSchreierMap k₀)_*ᵃ[l].obj
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
    (affineLine.geometricArtinSchreierMap k₀)_*ᵃ[l].obj
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (affineLine.geometricArtinSchreierMap k₀)_*ᵃ[l].map
      (ProEtale.adicLowerStarUnitIso l (affineLine.geometricTranslationIso k₀ c)).inv ≫
    (ProEtale.adicLowerStarComp l (affineLine.geometricTranslationIso k₀ c).hom
      (affineLine.geometricArtinSchreierMap k₀)).hom.app
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
    (ProEtale.adicLowerStarCongr l
      (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)

omit [Fact (ringChar k₀ ≠ l)] in
lemma artinSchreierTranslationSheafHom_hom (c : k₀) :
    (artinSchreierTranslationSheafHom l c).hom =
      (affineLine.geometricArtinSchreierMap k₀)_*[WeilCoefficients.{u} l].map
          (ProEtale.adicConstantSheafLowerStarIso l (affineLine.geometricTranslationIso k₀ c)).inv ≫
        (ProEtale.lowerStarComp (WeilCoefficients.{u} l)
          (affineLine.geometricTranslationIso k₀ c).hom
          (affineLine.geometricArtinSchreierMap k₀)).hom.app
          (ProEtale.adicConstantSheaf l
            (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (ProEtale.lowerStarCongr (WeilCoefficients.{u} l)
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          (ProEtale.adicConstantSheaf l
            (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  rfl

/-- The Weil structure of the pushforward `φ_* ℚ̄_ℓ` of the constant Weil sheaf, on underlying
sheaves: the exchange of `φ̄_*` with the Frobenius pushforwards followed by `φ̄_*` of the Weil
structure of `ℚ̄_ℓ`. -/
lemma WeilSheaf.lowerStar_adicConstant_str_hom_hom {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    ((WeilSheaf.lowerStar φ).obj (WeilSheaf.adicConstant k₀ l X)).obj.obj.str.hom =
      ((ProEtale.lowerStarComp _ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
            (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
            (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).symm).app
          -- Stated with this form of `ℚ̄_ℓ,X̄` rather than `ProEtale.adicConstantSheaf`: closing
          -- the goal up to the definitional unfolding of `WeilSheaf.adicConstant` times out in
          -- the kernel.
          (IsoAlgebra.carrier (WeilSheaf.adicConstant k₀ l X).obj).X ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)).hom := by
  rw [← Endofunctor.IsoAlgebra.str_hom, WeilSheaf.lowerStar_obj_obj_str, Iso.trans_hom,
    Mod.comp_hom', Functor.mapIso_hom, ProEtale.adicLowerStar_map_hom]
  erw [WeilSheaf.adicConstant_str_hom_hom]
  rw [ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.app_hom, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', ProEtale.adicLowerStarComp_hom_app_hom, ProEtale.adicLowerStarComp_inv_app_hom,
    ProEtale.adicLowerStarCongr_hom_app_hom]
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]

lemma artinSchreierPushforward_str_hom_hom :
    (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str.hom =
      ((ProEtale.lowerStarComp _ (affineLine.geometricArtinSchreierMap k₀)
            (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
            (affineLine.geometricArtinSchreierMap k₀)).symm).app
          (ProEtale.adicConstantSheaf l
            (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫
        (affineLine.geometricArtinSchreierMap k₀)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)).hom :=
  WeilSheaf.lowerStar_adicConstant_str_hom_hom (affineLine.artinSchreierMap k₀)

/-- The action of `σ_c` on `AS_* ℚ̄_ℓ` commutes with its Weil structure: the translation and
the Artin–Schreier map are defined over `k₀`, hence commute with the geometric Frobenius. -/
lemma artinSchreierTranslationSheafHom_comm (c : k₀) :
    (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀)).map
        (artinSchreierTranslationSheafHom l c) ≫
      (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str =
    (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str ≫
      artinSchreierTranslationSheafHom l c := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
    artinSchreierTranslationSheafHom_hom, artinSchreierPushforward_str_hom_hom]
  exact ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange l
    (affineLine.geometricArtinSchreierMap k₀)
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    (affineLine.geometricTranslationIso k₀ c)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
    (affineLine.geometricTranslation_comp_geometricGaloisFrobenius k₀ c) _ rfl

omit [Fact (ringChar k₀ ≠ l)] in
variable (l) in
/-- On sections over `U → 𝔸¹_{k̄}`, the action of `σ_c` on `ĀS_* ℚ̄_ℓ` pulls functions on
`U ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` back along `(u, x) ↦ (u, σ̄_c x)`. -/
lemma artinSchreierTranslationSheafHom_hom_app (c : k₀)
    (U : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt) :
    (artinSchreierTranslationSheafHom l c).hom.hom.app (op U) =
      (adicFunctionsPresheaf l).map (pullback.map U.hom (affineLine.geometricArtinSchreierMap k₀)
        U.hom (affineLine.geometricArtinSchreierMap k₀) (𝟙 _)
        (affineLine.geometricTranslationIso k₀ c).hom (𝟙 _) (by simp)
        (by simp [affineLine.geometricTranslation_comp_artinSchreierMap])).op := by
  rw [artinSchreierTranslationSheafHom_hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ProEtale.lowerStar_map_hom_app', unop_op,
    ProEtale.lowerStarComp_hom_app_hom_app, ProEtale.lowerStarCongr_hom_app_hom_app,
    ProEtale.adicConstantSheafLowerStarIso_inv_hom_app, ProEtale.adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

variable (l) in
/-- The action of the translation `σ_c : x ↦ x + c` on `AS_* ℚ̄_ℓ`, as an endomorphism of Weil
sheaves. -/
noncomputable def WeilSheaf.artinSchreierTranslationAction (c : k₀) :
    WeilSheaf.artinSchreierPushforward k₀ l ⟶ WeilSheaf.artinSchreierPushforward k₀ l :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨artinSchreierTranslationSheafHom l c, artinSchreierTranslationSheafHom_comm c⟩)

/-- The endomorphism `e_ψ = q⁻¹ ∑_{c ∈ k₀} ψ(-c) σ_c` of `AS_* ℚ̄_ℓ`, `q = #k₀`, the projector
onto the `ψ`-isotypic component. -/
noncomputable def WeilSheaf.artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf.artinSchreierPushforward k₀ l ⟶ WeilSheaf.artinSchreierPushforward k₀ l :=
  letI := Fintype.ofFinite k₀
  ∑ c : k₀, WeilSheaf.smulEnd ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) _ ≫
    WeilSheaf.artinSchreierTranslationAction l c

/-- After pullback along `ĀS`, the projector `e_ψ` becomes averaging followed by splitting
(`AlgebraicGeometry.affineLine.sum_apply_pullbackMap_translation`). -/
lemma affineLine.restriction_map_artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l)) :
    (ProEtale.localizationRestriction (WeilCoefficients.{u} l)
        (affineLine.geometricArtinSchreierMap k₀) inferInstance).map
      ((ObjectProperty.ι _ ⋙ IsoAlgebra.forget _).map (WeilSheaf.artinSchreierIdempotent ψ)).hom =
      affineLine.artinSchreierAverageHom l ψ ≫ affineLine.artinSchreierSplitHom l ψ := by
  let := Fintype.ofFinite k₀
  have hsum {F G : ProEtale.AdicSheaf l
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber}
      (s : Finset k₀) (f : k₀ → (F ⟶ G)) (W) :
      (∑ c ∈ s, f c).hom.hom.app W = ∑ c ∈ s, (f c).hom.hom.app W := by
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
  have hdown {M : Type u} [AddCommMonoid M] (s : Finset k₀) (f : k₀ → ULift.{u + 1} M) :
      (∑ c ∈ s, f c).down = ∑ c ∈ s, (f c).down :=
    map_sum AddEquiv.ulift f s
  ext V : 3
  rw [ProEtale.localizationRestriction_map_hom_app]
  simp only [WeilSheaf.artinSchreierIdempotent, Functor.map_sum, Functor.map_comp]
  ext ⟨h⟩
  simp only [hsum, ModuleCat.hom_sum, ModuleCat.hom_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun z ↦ ?_))
  rw [LinearMap.sum_apply, hdown, AddSubmonoidClass.coe_finsetSum, ContinuousMap.coe_sum,
    Finset.sum_apply]
  refine (Finset.sum_congr rfl fun c _ ↦ ?_).trans
    (affineLine.sum_apply_pullbackMap_translation V.unop.hom ψ h z)
  change (ModuleCat.Hom.hom ((artinSchreierTranslationSheafHom l c).hom.hom.app _)
    (ULift.up.{u + 1} ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) • ULift.up h)).down.1 z = _
  rw [artinSchreierTranslationSheafHom_hom_app]
  rfl

-- TODO(unify): lemma-artin-schreier-character-sheaf--1
/-- The Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line: the pullback along `x ↦ a x` of
the `ψ`-isotypic component `ℒ_ψ` of the pushforward of the constant sheaf along the
Artin–Schreier cover `u^q - u = x`, which is Galois over the line with group `k₀`, so that its
isotypic components are indexed by the additive characters of `k₀`. The component `ℒ_ψ` is the
image of the projector `e_ψ` (`AlgebraicGeometry.WeilSheaf.artinSchreierIdempotent`). It is
lisse of rank one and of weight zero. -/
noncomputable def artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.upperStar (affineLine.smul k₀ a)).obj (image (WeilSheaf.artinSchreierIdempotent ψ))

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

omit [Fact (ringChar k₀ ≠ l)] in
/-- The counit of `ĀS^* ⊣ ĀS_*`, computed by restriction, evaluates a function on
`V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` along the diagonal section `x ↦ (x, v x)`. -/
lemma affineLine.localizationRestrictionLowerStarAdjunction_counit_app_hom_app
    (V : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt) :
    ((ProEtale.localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ĀS
        inferInstance).counit.app
      (ProEtale.adicConstantSheaf l
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).hom.app (op V) =
      (adicFunctionsPresheaf l).map
        (pullback.lift (𝟙 V.left) V.hom (by simp) : V.left ⟶ pullback (V.hom ≫ ĀS) ĀS).op :=
  rfl


variable (l) in
/-- The evaluation `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the section `x ↦ (x, σ̄_c (v x))`, as a morphism
of sheaves of `ℚ̄_ℓ`-modules: the pullback of the translation `σ_c` followed by the counit of
`ĀS^* ⊣ ĀS_*`. -/
noncomputable def affineLine.artinSchreierEvalHom (c : k₀) :
    (ĀS)^*ᵃ[l].obj ((ĀS)_*ᵃ[l].obj
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ⟶
      ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (ĀS)^*ᵃ[l].map (artinSchreierTranslationSheafHom l c) ≫
    (ProEtale.adicUpperStarLowerStarAdjunction l ĀS).counit.app _

omit [Fact (ringChar k₀ ≠ l)] in
/-- On sections over `v : V ⟶ 𝔸¹_{k̄}`, the evaluation along `x ↦ (x, σ̄_c (v x))` pulls functions
on `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}` back along this section. -/
lemma affineLine.artinSchreierEvalHom_hom_app (c : k₀)
    (V : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt) :
    ((ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
        inferInstance).inv.app _ ≫ (affineLine.artinSchreierEvalHom l c).hom).hom.app (op V) =
      (adicFunctionsPresheaf l).map (affineLine.artinSchreierSection V.hom c).op := by
  have h₁ : (affineLine.artinSchreierEvalHom l c).hom =
      (ĀS)^*[WeilCoefficients.{u} l].map (artinSchreierTranslationSheafHom l c).hom ≫
        (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).counit.app
          (ProEtale.adicConstantSheaf l _) := by
    rw [affineLine.artinSchreierEvalHom, Mod.comp_hom', ProEtale.adicUpperStar_map_hom]
    erw [Adjunction.modAdjunction_counit_app_hom]
    rfl
  have h₂ := (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
    ĀS).leftAdjointUniq_hom_app_counit
      (ProEtale.localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ĀS
        inferInstance) (ProEtale.adicConstantSheaf l _)
  rw [h₁, ← Category.assoc, ← (ProEtale.upperStarIsoLocalizationRestriction
    (WeilCoefficients.{u} l) ĀS inferInstance).inv.naturality, Category.assoc]
  erw [← h₂, Iso.inv_hom_id_app_assoc]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ProEtale.localizationRestriction_map_hom_app]
  erw [artinSchreierTranslationSheafHom_hom_app,
    affineLine.localizationRestrictionLowerStarAdjunction_counit_app_hom_app]
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · rw [Category.assoc]
    erw [pullback.lift_fst, Category.comp_id, pullback.lift_fst,
      affineLine.artinSchreierSection_fst]
  · rw [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, affineLine.artinSchreierSection_snd]


omit [Fact (ringChar k₀ ≠ l)] in
/-- Morphisms into `ĀS^* ĀS_* ℚ̄_ℓ` are determined by their composites with the evaluations
along the sections `x ↦ (x, σ̄_c (v x))`, which cover `V ×_{𝔸¹_{k̄}} 𝔸¹_{k̄}`. -/
lemma affineLine.artinSchreierEvalHom_hom_ext
    {T : Sheaf (Scheme.ProEt.topology (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)}
    {f g : T ⟶ ((ĀS)^*ᵃ[l].obj ((ĀS)_*ᵃ[l].obj
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))).X}
    (h : ∀ c, f ≫ (affineLine.artinSchreierEvalHom l c).hom =
      g ≫ (affineLine.artinSchreierEvalHom l c).hom) : f = g := by
  let ε := ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS inferInstance
  suffices hε : f ≫ ε.hom.app _ = g ≫ ε.hom.app _ by
    have := congrArg (· ≫ ε.inv.app _) hε
    simp only [Category.assoc, Iso.hom_inv_id_app] at this
    erw [Category.comp_id, Category.comp_id] at this
    exact this
  ext ⟨V⟩ : 3
  ext x
  have key (c : k₀) (φ : T ⟶ affineLine.artinSchreierPullbackPushforward k₀ l) :
      (φ ≫ ε.inv.app _ ≫ (affineLine.artinSchreierEvalHom l c).hom).hom.app (op V) x =
        (adicFunctionsPresheaf l).map (affineLine.artinSchreierSection V.hom c).op
          (φ.hom.app (op V) x) := by
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply]
    erw [affineLine.artinSchreierEvalHom_hom_app]
    rfl
  have hc (c : k₀) := (key c _).symm.trans ((congrArg (fun φ ↦ φ.hom.app (op V) x)
    (show (f ≫ ε.hom.app _) ≫ (ε.inv.app _ ≫ (affineLine.artinSchreierEvalHom l c).hom) =
      (g ≫ ε.hom.app _) ≫ (ε.inv.app _ ≫ (affineLine.artinSchreierEvalHom l c).hom) by
        simpa using h c)).trans (key c _))
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun z ↦ ?_))
  have := congrArg (fun y ↦ y.down.1 (pullback.fst (V.hom ≫ ĀS) ĀS z))
    (hc (affineLine.artinSchreierIndex V.hom z))
  simp only [adicFunctionsPresheaf_map, ModuleCat.hom_ofHom] at this
  rw [← affineLine.artinSchreierSection_artinSchreierIndex V.hom z]
  exact this


omit [Fact (ringChar k₀ ≠ l)] in
/-- Evaluating the splitting `g ↦ ((x, σ̄_d (v x)) ↦ ψ(d) g(x))` along the section
`x ↦ (x, σ̄_c (v x))` is multiplication by `ψ(c)`. -/
lemma affineLine.artinSchreierSplitHom_comp_evalHom (ψ : AddChar k₀ (PadicAlgCl l)) (c : k₀) :
    affineLine.artinSchreierSplitHom l ψ ≫
      (ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
        inferInstance).inv.app ((ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).X
      ≫ (affineLine.artinSchreierEvalHom l c).hom =
      ULift.up (ψ c) • 𝟙 _ := by
  ext ⟨V⟩ : 3
  ext ⟨g⟩
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply]
  erw [affineLine.artinSchreierEvalHom_hom_app]
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  change ψ (affineLine.artinSchreierIndex V.hom (affineLine.artinSchreierSection V.hom c x)) *
    g.1 (pullback.fst (V.hom ≫ ĀS) ĀS (affineLine.artinSchreierSection V.hom c x)) = ψ c * g.1 x
  rw [affineLine.artinSchreierIndex_artinSchreierSection, affineLine.artinSchreierSection_fst_apply]


omit [Fact (ringChar k₀ ≠ l)] in
/-- The averaging map `h ↦ (x ↦ q⁻¹ ∑_c ψ(-c) h(x, σ̄_c (v x)))` is the corresponding linear
combination of the evaluations. -/
lemma affineLine.artinSchreierAverageHom_eq_sum (ψ : AddChar k₀ (PadicAlgCl l)) :
    letI := Fintype.ofFinite k₀
    affineLine.artinSchreierAverageHom l ψ =
      ∑ c : k₀, ULift.up ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) •
        ((ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
          inferInstance).inv.app ((ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).X
      ≫ (affineLine.artinSchreierEvalHom l c).hom) := by
  let := Fintype.ofFinite k₀
  have hsum {F G : Sheaf (Scheme.ProEt.topology
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (WeilCoefficients.{u} l)}
      (s : Finset k₀) (f : k₀ → (F ⟶ G)) (W) :
      (∑ c ∈ s, f c).hom.app W = ∑ c ∈ s, (f c).hom.app W := by
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
  have hdown {M : Type u} [AddCommMonoid M] (s : Finset k₀) (f : k₀ → ULift.{u + 1} M) :
      (∑ c ∈ s, f c).down = ∑ c ∈ s, (f c).down :=
    map_sum AddEquiv.ulift f s
  ext ⟨V⟩ : 3
  ext ⟨h⟩
  rw [hsum, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
  rw [hdown, AddSubmonoidClass.coe_finsetSum, ContinuousMap.coe_sum, Finset.sum_apply]
  change (affineLine.artinSchreierAverage l V.hom ψ h).1 x = _
  rw [affineLine.artinSchreierAverage_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  change _ = (ULift.up ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c)) •
    ((ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
      inferInstance).inv.app _ ≫ (affineLine.artinSchreierEvalHom l c).hom).hom.app (op V)
        (ULift.up h)).down.1 x
  erw [affineLine.artinSchreierEvalHom_hom_app]
  rfl


variable (l) in
/-- The averaging map, as a morphism of sheaves of `ℚ̄_ℓ`-modules: a linear combination of the
evaluations `AlgebraicGeometry.affineLine.artinSchreierEvalHom`. -/
noncomputable def affineLine.artinSchreierAverageModHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    (ĀS)^*ᵃ[l].obj ((ĀS)_*ᵃ[l].obj
      (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ⟶
      ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  letI := Fintype.ofFinite k₀
  ∑ c : k₀, affineLine.artinSchreierEvalHom l c ≫
    ProEtale.AdicSheaf.smul (ULift.up ((Nat.card k₀ : PadicAlgCl l)⁻¹ * ψ (-c))) _

omit [Fact (ringChar k₀ ≠ l)] in
/-- The underlying morphism of the averaging map of sheaves of modules is the averaging map. -/
lemma affineLine.artinSchreierAverageModHom_hom (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineLine.artinSchreierAverageModHom l ψ).hom =
      (ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
        inferInstance).hom.app ((ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).X
      ≫ affineLine.artinSchreierAverageHom l ψ := by
  let := Fintype.ofFinite k₀
  rw [affineLine.artinSchreierAverageHom_eq_sum, Preadditive.comp_sum,
    affineLine.artinSchreierAverageModHom]
  refine ((Mod.forget _).map_sum _ _).trans (Finset.sum_congr rfl fun c _ ↦ ?_)
  change (affineLine.artinSchreierEvalHom l c).hom ≫ (ULift.up _ • 𝟙 _) = _
  rw [Linear.comp_smul, Category.comp_id, Linear.comp_smul]
  congr 1
  erw [Iso.hom_inv_id_app_assoc]

variable (l) in
/-- The splitting map, as a morphism of sheaves of `ℚ̄_ℓ`-modules: it is `ℚ̄_ℓ`-linear, since its
composites with the evaluations are multiplications by scalars. -/
noncomputable def affineLine.artinSchreierSplitModHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (ĀS)^*ᵃ[l].obj ((ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :=
  Mod.homMk (affineLine.artinSchreierSplitHom l ψ ≫
      (ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
        inferInstance).inv.app ((ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).X) (by
    refine affineLine.artinSchreierEvalHom_hom_ext fun c ↦ ?_
    rw [Category.assoc, Category.assoc, affineLine.artinSchreierSplitHom_comp_evalHom,
      Category.assoc, Mod.act_hom, ← MonoidalCategory.whiskerLeft_comp_assoc,
      Category.assoc, affineLine.artinSchreierSplitHom_comp_evalHom]
    exact Mod.act_hom (ProEtale.AdicSheaf.smul (ULift.up (ψ c)) (ProEtale.AdicSheaf.unit l _)))

omit [Fact (ringChar k₀ ≠ l)] in
/-- The underlying morphism of the splitting map of sheaves of modules is the splitting map. -/
lemma affineLine.artinSchreierSplitModHom_hom (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineLine.artinSchreierSplitModHom l ψ).hom = affineLine.artinSchreierSplitHom l ψ ≫
      (ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS
        inferInstance).inv.app ((ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).X :=
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
/-- Averaging after splitting is the identity, as morphisms of sheaves of modules. -/
lemma affineLine.artinSchreierSplitModHom_averageModHom (ψ : AddChar k₀ (PadicAlgCl l)) :
    affineLine.artinSchreierSplitModHom l ψ ≫ affineLine.artinSchreierAverageModHom l ψ = 𝟙 _ := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', affineLine.artinSchreierSplitModHom_hom,
    affineLine.artinSchreierAverageModHom_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    affineLine.artinSchreierSplitHom_artinSchreierAverageHom]
  rfl


omit [Fact (ringChar k₀ ≠ l)] in
/-- An endomorphism of `ĀS_* ℚ̄_ℓ` which, after pullback along `ĀS`, is averaging followed by
splitting on underlying sheaves, is so as a morphism of sheaves of `ℚ̄_ℓ`-modules. -/
lemma affineLine.artinSchreierAverageModHom_splitModHom_of_restriction
    (ψ : AddChar k₀ (PadicAlgCl l))
    (f : (ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
      (ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hf : (ProEtale.localizationRestriction (WeilCoefficients.{u} l) ĀS inferInstance).map f.hom =
      affineLine.artinSchreierAverageHom l ψ ≫ affineLine.artinSchreierSplitHom l ψ) :
    affineLine.artinSchreierAverageModHom l ψ ≫ affineLine.artinSchreierSplitModHom l ψ =
      (ĀS)^*ᵃ[l].map f := by
  let ε := ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) ĀS inferInstance
  refine Mod.hom_ext _ _ (affineLine.artinSchreierEvalHom_hom_ext fun c ↦ ?_)
  have h₂ : (ĀS)^*[WeilCoefficients.{u} l].map f.hom ≫ (affineLine.artinSchreierEvalHom l c).hom =
      ε.hom.app ((ĀS)_*ᵃ[l].obj
        (ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).X
      ≫ affineLine.artinSchreierAverageHom l ψ ≫
        (ULift.up (ψ c) • 𝟙 _) :=
    calc _ = ε.hom.app _ ≫ (ε.inv.app _ ≫ (ĀS)^*[WeilCoefficients.{u} l].map f.hom) ≫
          (affineLine.artinSchreierEvalHom l c).hom := by
          rw [Category.assoc, Iso.hom_inv_id_app_assoc]
      _ = ε.hom.app _ ≫ (ProEtale.localizationRestriction (WeilCoefficients.{u} l) ĀS
            inferInstance).map f.hom ≫ ε.inv.app _ ≫ (affineLine.artinSchreierEvalHom l c).hom := by
          rw [← ε.inv.naturality, Category.assoc]
      _ = _ := by
          rw [hf, Category.assoc, affineLine.artinSchreierSplitHom_comp_evalHom]
  rw [Mod.comp_hom', affineLine.artinSchreierSplitModHom_hom, Category.assoc, Category.assoc,
    affineLine.artinSchreierSplitHom_comp_evalHom, affineLine.artinSchreierAverageModHom_hom,
    ProEtale.adicUpperStar_map_hom, h₂, Category.assoc]

-- Instance search for the (co)kernels in the category of sheaves of modules is slow.
/-- The `ψ`-isotypic component `ℒ_ψ` of `AS_* ℚ̄_ℓ`, the image of the projector `e_ψ`, is lisse
(of rank one): after pullback along the finite étale Galois cover `AS` itself, `AS_* ℚ̄_ℓ`
becomes `⨁_{c ∈ k₀} ℚ̄_ℓ` with `k₀` permuting the summands by translation, and the image of
`e_ψ` is the line spanned by `∑_c ψ(c) δ_c`. -/
theorem WeilSheaf.isLisse_image_artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l)) :
    (image (WeilSheaf.artinSchreierIdempotent ψ)).IsLisse := by
  let Φ := ObjectProperty.ι (WeilSheaf.objectProperty k₀ l (affineLine k₀)) ⋙
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have := ObjectProperty.preservesKernels_ι _ (cokernel.π (WeilSheaf.artinSchreierIdempotent ψ))
  have := ObjectProperty.preservesCokernels_ι _ (WeilSheaf.artinSchreierIdempotent ψ)
  have : HasColimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have : HasLimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  -- the underlying sheaf of modules of the image is the image of the underlying morphism, which
  -- becomes `ℚ̄_ℓ` after pullback along the pro-étale cover `ĀS`
  refine ProEtale.IsAdicLisseSheaf.of_iso (Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫
    Abelian.PreservesImage.iso Φ _ ≪≫ Abelian.imageIsoImage _).symm
    ⟨.singleton (affineLine.geometricArtinSchreierMap k₀),
      Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance, ?_⟩
  rintro _ _ ⟨⟩
  have hfac := affineLine.artinSchreierAverageModHom_splitModHom_of_restriction ψ
    (Φ.map (WeilSheaf.artinSchreierIdempotent ψ))
    (affineLine.restriction_map_artinSchreierIdempotent ψ)
  have hab := affineLine.artinSchreierSplitModHom_averageModHom (l := l) ψ
  have : IsSplitEpi (affineLine.artinSchreierAverageModHom l ψ) := ⟨⟨_, hab⟩⟩
  have : IsSplitMono (affineLine.artinSchreierSplitModHom l ψ) := ⟨⟨_, hab⟩⟩
  refine ⟨1, ⟨((ĀS)^*ᵃ[l].mapIso (Abelian.imageIsoImage _).symm ≪≫
    Abelian.PreservesImage.iso _ _ ≪≫ Abelian.imageIsoImage _) ≪≫
      (image.isoStrongEpiMono _ _ hfac).symm ≪≫
      (biproduct.isoProduct (fun _ : Fin 1 ↦ ProEtale.AdicSheaf.unit l
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫ productUniqueIso _).symm⟩⟩

/-- The Artin–Schreier sheaves are lisse: `ℒ_ψ` is lisse
(`AlgebraicGeometry.WeilSheaf.isLisse_image_artinSchreierIdempotent`), and pullback preserves
lisse sheaves. -/
theorem isLisse_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    (artinSchreier ψ a).IsLisse :=
  ProEtale.IsAdicLisseSheaf.upperStar _ (WeilSheaf.isLisse_image_artinSchreierIdempotent ψ)

end ArtinSchreier

section Constituent

variable (k₀) in
/-- The multiplication `x ↦ a x` of the geometric affine line `𝔸¹_{k̄}` by `a ∈ k̄`. It is
defined over `k̄`, not over `k₀`, and has no Frobenius structure. -/
noncomputable def affineLine.geometricSMul (a : AlgebraicClosure k₀) :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  pullback.lift
    (AffineSpace.homOfVector
      ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫
        (Scheme.specAlgebraicClosure k₀).hom)
      fun _ ↦ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure.appTop
          ((Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom a) *
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.appTop
          (AffineSpace.coord _ PUnit.unit))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (AffineSpace.homOfVector_over _ _)

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): definition-weil-representation
/-- `F.HasLinearArtinSchreierConstituent ψ a j` says that the restriction along `j : U ⟶ 𝔸¹` of
the geometric linear Artin–Schreier sheaf `ℒ_{ψ(a x)}`, for `a` in the algebraic closure of
`k₀`, is a constituent of the pullback of `F` to `U ⊗_{k₀} k̄`: a quotient of a lisse subsheaf
of the underlying sheaf of `F` on `Ū`, that is, a subquotient in the category of lisse sheaves,
a Jordan–Hölder constituent of the geometric monodromy representation
(`proposition-fourier-transform-middle-extension`). The geometric sheaf `ℒ_{ψ(a x)}` is the pullback
of the underlying sheaf of `ℒ_ψ` along the multiplication `x ↦ a x` of `𝔸¹_{k̄}`
(`AlgebraicGeometry.affineLine.geometricSMul`); it is defined over the finite subextension
`k₀(a)`, where it is `AlgebraicGeometry.artinSchreier` for the character `ψ ∘ Tr`, but only its
pullback to the geometric affine line is used here. Being lisse of rank one, it is irreducible,
so a subquotient isomorphic to it is an irreducible constituent. -/
def WeilSheaf.HasLinearArtinSchreierConstituent (F : WeilSheaf k₀ l U)
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : AlgebraicClosure k₀) (j : U ⟶ affineLine k₀)
    [j.IsOver (Spec (CommRingCat.of k₀))] : Prop :=
  ∃ (B : ProEtale.AdicSheaf l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (i : B ⟶ F.obj.carrier)
    (p : B ⟶ (Scheme.Hom.geometricFiberMap j (comp_over j _))^*ᵃ[l].obj
      ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj
        (artinSchreier ψ 1).obj.carrier)), ProEtale.IsAdicLisseSheaf B ∧ Mono i ∧ Epi p

end Constituent

section Fourier

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The internal hom `B ↦ [A, B]` out of a fixed pro-étale Weil sheaf, as a functor. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctor (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X where
  obj B := ProEtaleWeilSheaf.ihom k₀ l X A B
  map f := ObjectProperty.homMk ⟨(ProEtale.AdicSheaf.ihom A.carrier).map f.hom.f,
    ProEtaleWeilSheaf.ihom_map_comm A f⟩
  map_id _ := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((ProEtale.AdicSheaf.ihom A.carrier).map_id _))
  map_comp _ _ := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((ProEtale.AdicSheaf.ihom A.carrier).map_comp _ _))

instance (A : ProEtaleWeilSheaf k₀ l X) : (ProEtaleWeilSheaf.ihomFunctor k₀ l X A).Additive :=
  ⟨ObjectProperty.hom_ext _ (Algebra.Hom.ext (ProEtale.AdicSheaf.ihom A.carrier).map_add)⟩

variable (k₀ l X) in
/-- The internal hom out of a pro-étale Weil sheaf, followed by the forgetful functor, is the
internal hom of the underlying sheaves. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctorCompForgetIso (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.ihomFunctor k₀ l X A ⋙ IsoAlgebra.forget _ ≅
      IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.ihom A.carrier :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The internal hom out of a pro-étale Weil sheaf is left exact. -/
instance (A : ProEtaleWeilSheaf k₀ l X) :
    PreservesFiniteLimits (ProEtaleWeilSheaf.ihomFunctor k₀ l X A) := by
  have := (Mod.ihomAdjunction A.carrier).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (ProEtaleWeilSheaf.ihomFunctor k₀ l X A ⋙ IsoAlgebra.forget _) :=
    preservesFiniteLimits_of_natIso (ProEtaleWeilSheaf.ihomFunctorCompForgetIso k₀ l X A).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

omit [Fact (ringChar k₀ ≠ l)] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The internal hom out of a pro-étale Weil sheaf with lisse underlying sheaf is exact
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesFiniteColimits_ihom`). -/
theorem ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (A : ProEtaleWeilSheaf k₀ l X)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    PreservesFiniteColimits (ProEtaleWeilSheaf.ihomFunctor k₀ l X A) := by
  have := hA.preservesFiniteColimits_ihom
  have : PreservesFiniteColimits (ProEtaleWeilSheaf.ihomFunctor k₀ l X A ⋙ IsoAlgebra.forget _) :=
    preservesFiniteColimits_of_natIso (ProEtaleWeilSheaf.ihomFunctorCompForgetIso k₀ l X A).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- **Finiteness for the tensor product with a lisse Weil sheaf, on a single Weil sheaf.** For
a lisse Weil sheaf `F` and a Weil sheaf `G` placed in degree `0`, the right derived functor of
`[F, -]` on pro-étale Weil sheaves gives a Weil complex: `[F, -]` is exact
(`AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor`), so the derived
functor is `[F, G]` placed in degree `0`, and `[F, G]` is constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf`). -/
theorem WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor_singleFunctor
    (F : WeilSheaf k₀ l X) (hF : F.IsLisse) (G : ProEtaleWeilSheaf k₀ l X)
    (hG : WeilSheaf.objectProperty k₀ l X G) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor F.obj hF
  let G' : WeilSheaf k₀ l X := ⟨(ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).obj G,
    ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf hF hG⟩
  exact (WeilComplex.objectProperty k₀ l X).prop_of_iso
    (((ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).singleFunctorCompRightDerivedFunctorIso).app
      G).symm (WeilSheaf.toComplex.obj G').property

/-- **Finiteness for the tensor product with a lisse Weil sheaf.** For a lisse Weil sheaf `F`,
the right derived functor of `[F, -]` on pro-étale Weil sheaves carries Weil complexes to Weil
complexes: by dévissage along the truncation triangles (`DerivedCategory.prop_of_bounded`), the
derived functor being triangulated, this reduces to the case of a single Weil sheaf,
`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor_singleFunctor`. -/
theorem WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (hK : WeilComplex.objectProperty k₀ l X K) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor.obj K) :=
  _root_.DerivedCategory.prop_of_bounded
    ((WeilComplex.objectProperty k₀ l X).inverseImage
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor)
    (WeilSheaf.objectProperty k₀ l X)
    (fun G hG ↦ WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor_singleFunctor F hF G hG)
    K hK.1 hK.2

/-- The derived internal hom `R[F, -]` out of a lisse Weil sheaf `F`, on Weil complexes. -/
noncomputable def WeilComplex.ihomLisse (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory (WeilComplex.objectProperty k₀ l X)
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor
    (WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor F hF)

instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : (WeilComplex.ihomLisse F hF).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

noncomputable instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    (WeilComplex.ihomLisse F hF).CommShift ℤ :=
  ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The derived internal hom out of a lisse Weil sheaf is a triangulated functor. -/
instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : (WeilComplex.ihomLisse F hF).IsTriangulated :=
  ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

/-- The tensor product `G ⊗ -` with a lisse Weil sheaf `G`, on Weil complexes: the derived
internal hom out of the dual `G^∨`, `G` being locally free of finite rank over `ℚ̄_ℓ,X̄`. -/
noncomputable def WeilComplex.tensorLisse (G : WeilSheaf k₀ l X) (hG : G.IsLisse) :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  WeilComplex.ihomLisse (G.dual hG) hG.dual

/-- The affine plane `𝔸¹ ×_{k₀} 𝔸¹` over `k₀`, with its two projections and the multiplication
map to the affine line. -/
noncomputable def affinePlane : Scheme.{u} :=
  pullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

instance (G : WeilSheaf k₀ l X) (hG : G.IsLisse) : (WeilComplex.tensorLisse G hG).Additive := by
  unfold WeilComplex.tensorLisse
  infer_instance

noncomputable instance (G : WeilSheaf k₀ l X) (hG : G.IsLisse) :
    (WeilComplex.tensorLisse G hG).CommShift ℤ :=
  inferInstanceAs ((WeilComplex.ihomLisse (G.dual hG) hG.dual).CommShift ℤ)

/-- The tensor product with a lisse Weil sheaf is a triangulated functor. -/
instance (G : WeilSheaf k₀ l X) (hG : G.IsLisse) :
    (WeilComplex.tensorLisse G hG).IsTriangulated :=
  inferInstanceAs ((WeilComplex.ihomLisse (G.dual hG) hG.dual).IsTriangulated)

section AffineSpaceFourier

variable (ι : Type u) [Fintype ι]

/-- The kernel `⟨-, -⟩^* ℒ_ψ` of the Fourier–Deligne transform on `𝔸^ι ×_{k₀} 𝔸^ι`, the
pullback of the Artin–Schreier sheaf along the standard pairing. -/
noncomputable def affineSpaceFourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf k₀ l (affineSpacePair ι k₀) :=
  (WeilSheaf.upperStar (affineSpacePair.pairing ι k₀)).obj (artinSchreier ψ 1)

/-- The kernel of the Fourier–Deligne transform on `𝔸^ι` is lisse, as a pullback of the lisse
Artin–Schreier sheaf. -/
theorem isLisse_affineSpaceFourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierKernel ι ψ).IsLisse :=
  ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreier ψ 1)

/-- The Fourier–Deligne transform `FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ)[r]` from Weil
complexes on `𝔸^ι` to Weil complexes on the dual affine space, `r = #ι`, with Laumon's shift by
the relative dimension. It is a triangulated functor between the triangulated categories of
Weil complexes. -/
noncomputable def affineSpaceFourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)) ⥤
      WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)) :=
  WeilComplex.upperStar (affineSpacePair.fst ι k₀) ⋙
    WeilComplex.tensorLisse (affineSpaceFourierKernel ι ψ)
      (isLisse_affineSpaceFourierKernel ι ψ) ⋙
    WeilComplex.derivedLowerShriek k₀ l (affineSpacePair.snd ι k₀) ⋙
    shiftFunctor _ (Fintype.card ι : ℤ)

instance affineSpaceFourierTransform.additive (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierTransform (l := l) ι ψ).Additive := by
  unfold affineSpaceFourierTransform
  infer_instance

noncomputable instance affineSpaceFourierTransform.commShift (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierTransform (l := l) ι ψ).CommShift ℤ := by
  unfold affineSpaceFourierTransform
  infer_instance

/-- The Fourier–Deligne transform on `𝔸^ι` is a triangulated functor, as a composite of the
triangulated functors `pr₁^*`, `- ⊗ ⟨-, -⟩^* ℒ_ψ`, `Rpr₂!` and the shift. -/
instance affineSpaceFourierTransform.isTriangulated (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierTransform (l := l) ι ψ).IsTriangulated := by
  unfold affineSpaceFourierTransform
  infer_instance

end AffineSpaceFourier

/-- `affinePlane k₀` is the affine plane `𝔸¹ ×_{k₀} 𝔸¹` over `k₀`, with its two projections and
the multiplication map to the affine line: notation for the case `ι = PUnit` of
`AlgebraicGeometry.affineSpacePair`, so that the line and the `𝔸^ι` declarations elaborate to the
same scheme and its `Over` structure and instances are those of `affineSpacePair`. -/
macro "affinePlane " k₀:term:max : term => `(AlgebraicGeometry.affineSpacePair PUnit $k₀)

variable (k₀) in
/-- The first projection `pr₁ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`. -/
noncomputable def affinePlane.fst : affinePlane k₀ ⟶ affineLine k₀ :=
  affineSpacePair.fst PUnit.{u + 1} k₀

variable (k₀) in
/-- The second projection `pr₂ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`. -/
noncomputable def affinePlane.snd : affinePlane k₀ ⟶ affineLine k₀ :=
  affineSpacePair.snd PUnit.{u + 1} k₀

instance : (affinePlane.fst k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  inferInstanceAs ((affineSpacePair.fst PUnit.{u + 1} k₀).IsOver (Spec (CommRingCat.of k₀)))

instance : (affinePlane.snd k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  inferInstanceAs ((affineSpacePair.snd PUnit.{u + 1} k₀).IsOver (Spec (CommRingCat.of k₀)))

instance : IsSeparated (affinePlane.snd k₀) :=
  inferInstanceAs (IsSeparated (affineSpacePair.snd PUnit.{u + 1} k₀))

instance : QuasiCompact (affinePlane.snd k₀) :=
  inferInstanceAs (QuasiCompact (affineSpacePair.snd PUnit.{u + 1} k₀))

instance : LocallyOfFiniteType (affinePlane.snd k₀) :=
  inferInstanceAs (LocallyOfFiniteType (affineSpacePair.snd PUnit.{u + 1} k₀))

variable (k₀) in
/-- The multiplication `μ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`, `(x, y) ↦ x y`. -/
noncomputable def affinePlane.mul : affinePlane k₀ ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) fun _ ↦
    (affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
      (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)

instance : (affinePlane.mul k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

variable (k₀) in
omit [Finite k₀] in
/-- For `ι = PUnit`, the product `𝔸^ι ×_{k₀} 𝔸^ι` is the affine plane and the standard pairing
is the multiplication `μ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`: a one-term sum is the product. -/
theorem affineSpacePair.pairing_punit :
    affineSpacePair.pairing PUnit.{u + 1} k₀ = affinePlane.mul k₀ := by
  refine congrArg (AffineSpace.homOfVector _) (funext fun _ ↦ ?_)
  rw [AffineSpace.stdPairing, Fintype.sum_unique]
  rfl

/-- The kernel `μ^* ℒ_ψ` of the Fourier–Deligne transform on `𝔸¹ ×_{k₀} 𝔸¹`: the case
`ι = PUnit` of `AlgebraicGeometry.affineSpaceFourierKernel`. -/
noncomputable def fourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf k₀ l (affinePlane k₀) :=
  affineSpaceFourierKernel PUnit.{u + 1} ψ

/-- The kernel of the Fourier–Deligne transform on the line is the pullback `μ^* ℒ_ψ` of the
Artin–Schreier sheaf along the multiplication, since for `ι = PUnit` the pairing is the
multiplication (`AlgebraicGeometry.affineSpacePair.pairing_punit`). -/
noncomputable def fourierKernelIso (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierKernel ψ ≅ (WeilSheaf.upperStar (affinePlane.mul k₀)).obj (artinSchreier ψ 1) :=
  (WeilSheaf.upperStarCongr (X := affineSpacePair PUnit.{u + 1} k₀)
    (affineSpacePair.pairing_punit k₀)).app (artinSchreier ψ 1)

/-- The kernel of the Fourier–Deligne transform is lisse, as a pullback of the lisse
Artin–Schreier sheaf. -/
theorem isLisse_fourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierKernel ψ).IsLisse :=
  isLisse_affineSpaceFourierKernel PUnit.{u + 1} ψ

-- TODO(unify): sec-Fourier-inversion
/-- The Fourier–Deligne transform `FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]` from Weil complexes
on the affine line to Weil complexes on the dual affine line, with Laumon's shift by the
relative dimension one: the case `ι = PUnit` of `AlgebraicGeometry.affineSpaceFourierTransform`.
It is a triangulated functor between the triangulated categories of Weil complexes. -/
noncomputable def fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l (affineLine k₀) ⥤ WeilComplex k₀ l (affineLine k₀) :=
  affineSpaceFourierTransform PUnit.{u + 1} ψ

/-- The Fourier–Deligne transform of the line is `Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]`. -/
theorem fourierTransform_eq (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierTransform ψ = WeilComplex.upperStar (affinePlane.fst k₀) ⋙
      WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ) ⋙
      WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀) ⋙
      shiftFunctor _ (1 : ℤ) :=
  rfl

-- TODO(unify): sec-Fourier-inversion
instance (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierTransform (l := l) ψ).Additive :=
  inferInstanceAs (affineSpaceFourierTransform (l := l) PUnit.{u + 1} ψ).Additive

-- TODO(unify): sec-Fourier-inversion
noncomputable instance (ψ : AddChar k₀ (PadicAlgCl l)) :
    (fourierTransform (l := l) ψ).CommShift ℤ :=
  inferInstanceAs ((affineSpaceFourierTransform (l := l) PUnit.{u + 1} ψ).CommShift ℤ)

-- TODO(unify): sec-Fourier-inversion
/-- The Fourier–Deligne transform is a triangulated functor, as a composite of the triangulated
functors `pr₁^*`, `- ⊗ μ^* ℒ_ψ`, `Rpr₂!` and the shift. -/
instance (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierTransform (l := l) ψ).IsTriangulated :=
  inferInstanceAs (affineSpaceFourierTransform (l := l) PUnit.{u + 1} ψ).IsTriangulated

end Fourier

end AlgebraicGeometry
