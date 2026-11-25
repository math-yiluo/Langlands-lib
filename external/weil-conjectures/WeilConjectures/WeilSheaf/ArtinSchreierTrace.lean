/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Trace
public import WeilConjectures.WeilSheaf.ArtinSchreierFrobenius
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.TraceFunctionOps
public import WeilConjectures.WeilSheaf.Stalk

/-!

# The trace function of the Artin–Schreier sheaf

Let `k₀` be a finite field with `q` elements, `ψ` an additive character of `k₀` with values in
`ℚ̄_ℓ` and `a ∈ k₀`. The trace function of the Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine
line is `x ↦ ψ(Tr_{𝔽_{qⁿ}/k₀}(a x))` on the `𝔽_{qⁿ}`-rational points: at a point `x`, the local
geometric Frobenius acts on the functions on the fibre `{y : y ^ q - y = a x}` of the
Artin–Schreier covering as the translation by `Tr_{𝔽_{qⁿ}/k₀}(a x)`, since
`y ^ (q ^ n) = y + ∑_{i < n} (a x) ^ (q ^ i)`, and so on the `ψ`-isotypic part by
`ψ(Tr_{𝔽_{qⁿ}/k₀}(a x))`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`
(`lemma-artin-schreier-character-sheaf--6`): the trace
  function of `ℒ_{ψ(a x)}`.
- `AlgebraicGeometry.affineLine.frobeniusEnd_stalkAt_artinSchreierImage`: the local Frobenius of
  `ℒ_ψ` at a geometric point `s = ĀS ∘ t` with `σⁿ ∘ t = Frⁿ ∘ σ̄_d ∘ t` is the scalar `ψ(-d)`.
- `AlgebraicGeometry.affineLine.exists_comp_geometricArtinSchreierMap_eq`: the geometric point
  over an `𝔽_{qⁿ}`-rational point `x` lifts to a point `t` of the Artin–Schreier cover with
  `σⁿ ∘ t = Frⁿ ∘ σ̄_{-Tr(x)} ∘ t`.

## Implementation notes

The stalks are computed through the Artin–Schreier cover itself. After pullback along `ĀS`,
`ℒ_ψ` becomes `ℚ̄_ℓ` (`AlgebraicGeometry.affineLine.exists_iso_artinSchreierImage`), through the
evaluation `ĀS^* ℒ_ψ ⟶ ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` at the point of the fibre given by the cover. This
trivialisation is compatible with the Weil structures
(`AlgebraicGeometry.affineLine.artinSchreierImageEval_frobenius`, from the compatibility of the
counit of `ĀS^* ⊣ ĀS_*`, `AlgebraicGeometry.affineLine.artinSchreierCounit_frobenius`), and its
pullback along a translation `σ̄_c` is the evaluation at the translated point of the fibre, which
is `ψ(c)` times the trivialisation
(`AlgebraicGeometry.affineLine.artinSchreierImageEval_translation`). The Frobenius of the stalk
of `ℒ_ψ` at `s = ĀS ∘ t` thus becomes, through
`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp_stalkObjHomOfUpperStar`,
a transport of the stalk of `ℚ̄_ℓ` from `t` to `σ̄_d ∘ t` along canonical morphisms, which is the
identity (`AlgebraicGeometry.ProEtale.globalSectionsTransport_comp_globalSectionsTransport_eq_id`),
followed by the multiplication by `ψ(-d)`.

The geometric Frobenius `σ` of `k̄` is the inverse of `y ↦ y ^ q`: on the fibre
`{y : y ^ q - y = x}`, `y ^ (q ^ n) = y + Tr(x)`, so `σⁿ(y) = y - Tr(x)`, the translation by
`d = -Tr(x)`, and the local Frobenius is `ψ(-d) = ψ(Tr(x))`, as stated.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

section Trivialization

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- The inclusion `ℒ_ψ ⟶ ĀS_* ℚ̄_ℓ` of the `ψ`-isotypic component, on underlying sheaves. -/
noncomputable def affineLine.artinSchreierImageι :
    (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ⟶
      (ĀS)_*[WeilCoefficients.{u} l].obj
        (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (WeilSheaf.sheafFunctor k₀ l (affineLine k₀)).map (image.ι (WeilSheaf.artinSchreierIdempotent ψ))

/-- **The trivialisation of `ĀS^* ℒ_ψ`.** After pullback along the geometric Artin–Schreier map,
the `ψ`-isotypic component `ℒ_ψ` becomes `ℚ̄_ℓ`: there is an isomorphism `E : ĀS^* ℒ_ψ ≅ ℚ̄_ℓ`
through which the evaluation along `x ↦ (x, σ̄_c x)` is multiplication by `ψ(c)`. It comes from
the two epi-mono factorisations of `ĀS^* e_ψ`, through `ĀS^* ℒ_ψ` and through the averaging and
splitting maps
(`AlgebraicGeometry.affineLine.artinSchreierAverageModHom_splitModHom_of_restriction`). -/
theorem affineLine.exists_iso_artinSchreierImage :
    ∃ E : (ĀS)^*[WeilCoefficients.{u} l].obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ≅
        ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      ∀ c : k₀, (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierImageι ψ) ≫
        (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierTranslation l c) ≫
          affineLine.artinSchreierCounit k₀ l = E.hom ≫ (ULift.up (ψ c) • 𝟙 _) := by
  set e := WeilSheaf.artinSchreierIdempotent ψ
  have hfac := affineLine.artinSchreierAverageModHom_splitModHom_of_restriction ψ
    ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).map e)
    (affineLine.restriction_map_artinSchreierIdempotent ψ)
  have hab := affineLine.artinSchreierSplitModHom_averageModHom (l := l) ψ
  have hfac' : (affineLine.artinSchreierAverageModHom l ψ).hom ≫
      (affineLine.artinSchreierSplitModHom l ψ).hom =
      (ĀS)^*[WeilCoefficients.{u} l].map ((WeilSheaf.sheafFunctor k₀ l (affineLine k₀)).map e) := by
    rw [← Mod.comp_hom', hfac, ProEtale.adicUpperStar_map_hom]
    rfl
  have hab' : (affineLine.artinSchreierSplitModHom l ψ).hom ≫
      (affineLine.artinSchreierAverageModHom l ψ).hom = 𝟙 _ := by
    rw [← Mod.comp_hom', hab]
    rfl
  have : IsSplitEpi (affineLine.artinSchreierAverageModHom l ψ).hom := ⟨⟨_, hab'⟩⟩
  have : IsSplitMono (affineLine.artinSchreierSplitModHom l ψ).hom := ⟨⟨_, hab'⟩⟩
  have hp : (ĀS)^*[WeilCoefficients.{u} l].map ((WeilSheaf.sheafFunctor k₀ l (affineLine k₀)).map
      (factorThruImage e)) ≫ (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierImageι ψ) =
      (ĀS)^*[WeilCoefficients.{u} l].map ((WeilSheaf.sheafFunctor k₀ l (affineLine k₀)).map e) := by
    rw [affineLine.artinSchreierImageι, ← Functor.map_comp, ← Functor.map_comp, image.fac]
  have : Epi ((ĀS)^*[WeilCoefficients.{u} l].map
      ((WeilSheaf.sheafFunctor k₀ l (affineLine k₀)).map (factorThruImage e))) := inferInstance
  have : Mono (affineLine.artinSchreierImageι ψ) := by
    unfold affineLine.artinSchreierImageι
    infer_instance
  have : Mono ((ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierImageι ψ)) :=
    inferInstance
  have : StrongEpi ((ĀS)^*[WeilCoefficients.{u} l].map
      ((WeilSheaf.sheafFunctor k₀ l (affineLine k₀)).map (factorThruImage e))) :=
    strongEpi_of_epi _
  let i₁ := image.isoStrongEpiMono _ _ hp
  let i₂ := image.isoStrongEpiMono _ _ hfac'
  refine ⟨i₁ ≪≫ i₂.symm, fun c ↦ ?_⟩
  have hm : (i₁ ≪≫ i₂.symm).hom ≫ (affineLine.artinSchreierSplitModHom l ψ).hom =
      (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierImageι ψ) := by
    simp only [i₁, i₂, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      image.isoStrongEpiMono_inv_comp_mono,
      image.isoStrongEpiMono_hom_comp_ι]
  rw [← affineLine.artinSchreierEvalHom_hom, ← hm, Category.assoc,
    affineLine.artinSchreierSplitModHom_hom, Category.assoc,
    affineLine.artinSchreierSplitHom_comp_evalHom]

/-- The evaluation `ĀS^* ℒ_ψ ⟶ ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the section `x ↦ (x, σ̄_c x)` of the
fibre product. For `c = 0` it is the counit, and it trivialises `ĀS^* ℒ_ψ`. -/
noncomputable def affineLine.artinSchreierImageEval (c : k₀) :
    (ĀS)^*[WeilCoefficients.{u} l].obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ⟶
      (WeilSheaf.adicConstant k₀ l (affineLine k₀)).obj.carrier.X :=
  (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierImageι ψ) ≫
    (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierTranslation l c) ≫
      affineLine.artinSchreierCounit k₀ l

/-- The trivialisation `ĀS^* ℒ_ψ ≅ ℚ̄_ℓ` is compatible with the Weil structures of `ℒ_ψ` and of
`ℚ̄_ℓ`, in the form required by
`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp_stalkObjHomOfUpperStar`.
-/
lemma affineLine.artinSchreierImageEval_frobenius :
    (ProEtale.upperStarComp _
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      ĀS).hom.app (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          (affineLine.artinSchreierImageEval ψ 0) ≫
        (WeilSheaf.adicConstant k₀ l (affineLine k₀)).frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          (affineLine.artinSchreierMap k₀) (comp_over _ _)).symm).hom.app
          (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ≫
        (ProEtale.upperStarComp _ ĀS
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
          (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ≫
        (ĀS)^*[_].map (image (WeilSheaf.artinSchreierIdempotent ψ)).frobeniusStr ≫
        affineLine.artinSchreierImageEval ψ 0 := by
  have hι : ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
      (affineLine.artinSchreierImageι ψ) ≫ affineLine.artinSchreierPushforwardStr k₀ l =
      (image (WeilSheaf.artinSchreierIdempotent ψ)).frobeniusStr ≫
        affineLine.artinSchreierImageι ψ := by
    have h := WeilSheaf.frobeniusStr_naturality (image.ι (WeilSheaf.artinSchreierIdempotent ψ))
    rw [affineLine.frobeniusStr_artinSchreierPushforward] at h
    exact h
  have n₁ := ProEtale.upperStarComp_hom_app_comp_map_map (A := WeilCoefficients.{u} l)
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ĀS
    (affineLine.artinSchreierImageι ψ)
  have n₂ := ProEtale.upperStarComp_hom_app_comp_map_map (A := WeilCoefficients.{u} l) ĀS
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
    (affineLine.artinSchreierImageι ψ)
  have n₃ := ProEtale.upperStarCongr_hom_app_comp_map (A := WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      (affineLine.artinSchreierMap k₀) (comp_over _ _)).symm (affineLine.artinSchreierImageι ψ)
  have key := affineLine.artinSchreierCounit_frobenius (k₀ := k₀) (l := l)
  rw [affineLine.artinSchreierImageEval, affineLine.artinSchreierTranslation_zero,
    CategoryTheory.Functor.map_id, Category.id_comp, WeilSheaf.frobeniusStr_adicConstant,
    Functor.map_comp, Category.assoc, reassoc_of% n₁, key, ← Functor.map_comp_assoc, ← hι,
    Functor.map_comp_assoc, reassoc_of% n₂, reassoc_of% n₃]

/-- The pullback along the translation `σ̄_c` of the trivialisation of `ĀS^* ℒ_ψ` is the
evaluation along `x ↦ (x, σ̄_c x)`. -/
lemma affineLine.artinSchreierImageEval_translation (c : k₀) :
    (ProEtale.upperStarComp _ (affineLine.geometricTranslationIso k₀ c).hom ĀS).hom.app
        (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ≫
        ((affineLine.geometricTranslationIso k₀ c).hom)^*[_].map
          (affineLine.artinSchreierImageEval ψ 0) ≫
        ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ c).hom =
      (ProEtale.upperStarCongr _
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X ≫
        affineLine.artinSchreierImageEval ψ c := by
  have n₁ := ProEtale.upperStarComp_hom_app_comp_map_map (A := WeilCoefficients.{u} l)
    (affineLine.geometricTranslationIso k₀ c).hom ĀS (affineLine.artinSchreierImageι ψ)
  have n₂ := ProEtale.upperStarCongr_hom_app_comp_map (A := WeilCoefficients.{u} l)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
    (affineLine.artinSchreierImageι ψ)
  rw [affineLine.artinSchreierImageEval, affineLine.artinSchreierTranslation_zero,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc,
    reassoc_of% n₁, affineLine.artinSchreierCounit_translation, affineLine.artinSchreierImageEval,
    reassoc_of% n₂]

/-- **The local Frobenius of `ℒ_ψ`.** Let `t` be a geometric point of the geometric affine line,
`s = ĀS ∘ t` its image, fixed by `Frⁿ` up to `σⁿ`, and suppose that `σⁿ ∘ t = Frⁿ ∘ σ̄_d ∘ t`:
the two lifts `σⁿ ∘ t` and `Frⁿ ∘ t` of `σⁿ ∘ s = Frⁿ ∘ s` differ by the translation `σ̄_d`.
Then the Frobenius of the stalk of `ℒ_ψ` at `s` relative to `𝔽_{qⁿ}` is the scalar `ψ(-d)`, the
stalk being a line. Through the trivialisation `ĀS^* ℒ_ψ ≅ ℚ̄_ℓ`, which is compatible with the Weil
structures, the Frobenius becomes the transport of the stalk of `ℚ̄_ℓ` from `t` to `σ̄_d ∘ t`,
trivial on `ℚ̄_ℓ`, while moving back along `σ̄_d` multiplies the trivialisation by `ψ(d)`. -/
theorem affineLine.frobeniusEnd_stalkAt_artinSchreierImage {n : ℕ} (hn : 1 ≤ n)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (d : k₀)
    (hX : (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ t =
      (t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom)
    (hs : (t ≫ ĀS) ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ (t ≫ ĀS)) :
    ((image (WeilSheaf.artinSchreierIdempotent ψ)).stalkAt (t ≫ ĀS) n hs).frobeniusEnd =
        ψ (-d) • LinearMap.id ∧
      Module.finrank (PadicAlgCl l)
        ((image (WeilSheaf.artinSchreierIdempotent ψ)).stalkAt (t ≫ ĀS) n hs).carrier = 1 := by
  obtain ⟨E, hE⟩ := affineLine.exists_iso_artinSchreierImage ψ
  have hθ (c : k₀) : affineLine.artinSchreierImageEval ψ c = E.hom ≫ (ULift.up (ψ c) • 𝟙 _) :=
    hE c
  have hθ₀ : affineLine.artinSchreierImageEval ψ 0 = E.hom := by
    rw [hθ, AddChar.map_zero_eq_one]
    exact (congrArg (E.hom ≫ ·) (one_smul _ _)).trans (Category.comp_id _)
  have hθd : affineLine.artinSchreierImageEval ψ d =
      affineLine.artinSchreierImageEval ψ 0 ≫ (ULift.up (ψ d) • 𝟙 _) := by
    rw [hθ₀, hθ]
    rfl
  have hiso : IsIso (affineLine.artinSchreierImageEval ψ 0) := by
    rw [hθ₀]
    infer_instance
  -- the Frobenius, through the trivialisation
  have hY : (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ (t ≫ ĀS) =
      ((t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫ ĀS) ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom := by
    rw [Category.assoc t, affineLine.geometricTranslation_comp_artinSchreierMap, hs]
  have h₁ := WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp_stalkObjHomOfUpperStar
    (φ := affineLine.artinSchreierMap k₀) (G := WeilSheaf.adicConstant k₀ l (affineLine k₀))
    (θ := affineLine.artinSchreierImageEval ψ 0)
    (affineLine.artinSchreierImageEval_frobenius ψ) n hn hX hY
  -- moving back along the translation `σ̄_d`
  have hR : 𝟙 _ ≫ (t ≫ (affineLine.geometricTranslationIso k₀ d).hom) =
      t ≫ (affineLine.geometricTranslationIso k₀ d).hom := Category.id_comp _
  have p' : (t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫ ĀS = t ≫ ĀS := by
    rw [Category.assoc, affineLine.geometricTranslation_comp_artinSchreierMap]
  have h'' : (𝟙 _ ≫ (Iso.refl (Spec (.of (AlgebraicClosure k₀)))).hom) ≫
      ((t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫ ĀS) =
      t ≫ ((affineLine.geometricTranslationIso k₀ d).hom ≫ ĀS) := by
    simp
  have hτ : 𝟙 _ ≫ (Iso.refl (Spec (.of (AlgebraicClosure k₀)))).hom =
      (Iso.refl (Spec (.of (AlgebraicClosure k₀)))).hom := Category.id_comp _
  have h₂ : WeilSheaf.stalkObjHomOfUpperStar (affineLine.artinSchreierMap k₀)
      (WeilSheaf.adicConstant k₀ l (affineLine k₀)) (affineLine.artinSchreierImageEval ψ 0)
      (t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫
      ProEtale.globalSectionsTransport _ hR (ProEtale.upperStarAdicConstantSheafHom l
        (affineLine.geometricTranslationIso k₀ d).hom) =
      eqToHom (congrArg (fun s ↦ (Sheaf.Γ _ _).obj ((s)^*[WeilCoefficients.{u} l].obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier.X)) p') ≫
        WeilSheaf.stalkObjHomOfUpperStar (affineLine.artinSchreierMap k₀)
          (WeilSheaf.adicConstant k₀ l (affineLine k₀)) (affineLine.artinSchreierImageEval ψ 0) t ≫
          (ULift.up (ψ d) • 𝟙 _) := by
    rw [WeilSheaf.stalkObjHomOfUpperStar, ProEtale.globalSectionsTransport_comp _ _ _ h'',
      ProEtale.globalSectionsTransport_congr _ _
        (affineLine.geometricTranslation_comp_artinSchreierMap k₀ d) _ _
        (affineLine.artinSchreierImageEval_translation ψ d),
      ProEtale.globalSectionsTransport_congr_left _ _ hτ,
      ← ProEtale.eqToHom_comp_globalSectionsTransport _ (Category.id_comp (t ≫ ĀS)) p', hθd,
      WeilSheaf.globalSectionsTransport_comp_smul
        (N := (WeilSheaf.adicConstant k₀ l (affineLine k₀)).obj.carrier)]
    rfl
  -- the Frobenius of the stalks of `ℚ̄_ℓ` is trivial
  have h₃ : ProEtale.globalSectionsTransport _ hX
      ((WeilSheaf.adicConstant k₀ l (affineLine k₀)).frobeniusPowStr n) ≫
      ProEtale.globalSectionsTransport _ hR (ProEtale.upperStarAdicConstantSheafHom l
        (affineLine.geometricTranslationIso k₀ d).hom) = 𝟙 _ := by
    rw [WeilSheaf.frobeniusPowStr_adicConstant k₀ l (affineLine k₀) n hn]
    exact ProEtale.globalSectionsTransport_comp_globalSectionsTransport_eq_id hX hR
  have p : t ≫ ĀS = (t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫ ĀS := p'.symm
  have h₄ := ProEtale.globalSectionsTransport_comp_eqToHom hs.symm hY p
    ((image (WeilSheaf.artinSchreierIdempotent ψ)).frobeniusPowStr n)
  set S := WeilSheaf.stalkObjHomOfUpperStar (affineLine.artinSchreierMap k₀)
    (WeilSheaf.adicConstant k₀ l (affineLine k₀)) (affineLine.artinSchreierImageEval ψ 0) t
  have key : ProEtale.globalSectionsTransport _ hs.symm
      ((image (WeilSheaf.artinSchreierIdempotent ψ)).frobeniusPowStr n) ≫ S ≫
        (ULift.up (ψ d) • 𝟙 _) = S := by
    have k := h₁ =≫ ProEtale.globalSectionsTransport _ hR
      (ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ d).hom)
    simp only [Category.assoc] at k
    rw [h₃] at k
    erw [Category.comp_id] at k
    rw [h₂, ← h₄, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp] at k
    exact k
  have hc : (ULift.up (ψ d) • 𝟙 ((WeilSheaf.adicConstant k₀ l (affineLine k₀)).stalkObj t)) ≫
      (ULift.up (ψ (-d)) • 𝟙 _) = 𝟙 _ := by
    have h1 : ULift.up (ψ d) * ULift.up (ψ (-d)) = (1 : ULift.{u + 1} (PadicAlgCl l)) :=
      ULift.ext ((AddChar.map_add_eq_mul ψ d (-d)).symm.trans
        (by rw [add_neg_cancel, AddChar.map_zero_eq_one]; rfl))
    rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul, h1, one_smul]
  have e₁ := key =≫ (ULift.up (ψ (-d)) • 𝟙 _)
  simp only [Category.assoc, hc, Category.comp_id] at e₁
  have hT : ProEtale.globalSectionsTransport _ hs.symm
      ((image (WeilSheaf.artinSchreierIdempotent ψ)).frobeniusPowStr n) =
      ULift.up (ψ (-d)) • 𝟙 _ :=
    (cancel_mono S).1 (e₁.trans (by
      simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]))
  refine ⟨?_, ?_⟩
  · rw [WeilSheaf.frobeniusEnd_stalkAt, hT]
    rfl
  · exact (WeilCoefficients.linearEquivOfIso (asIso S)).finrank_eq.trans
      (ProEtale.finrank_globalSections_upperStar_adicConstantSheaf t)

/-- The trace of the local Frobenius of `ℒ_ψ` at a geometric point `s = ĀS ∘ t` with
`σⁿ ∘ t = Frⁿ ∘ σ̄_d ∘ t` is `ψ(-d)`
(`AlgebraicGeometry.affineLine.frobeniusEnd_stalkAt_artinSchreierImage`). -/
theorem affineLine.trace_frobeniusEnd_stalkAt_artinSchreierImage {n : ℕ} (hn : 1 ≤ n)
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hs : s ≫ ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ s)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) (ht : t ≫ ĀS = s) (d : k₀)
    (hX : (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ t =
      (t ≫ (affineLine.geometricTranslationIso k₀ d).hom) ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom) :
    LinearMap.trace (PadicAlgCl l) _
      ((image (WeilSheaf.artinSchreierIdempotent ψ)).stalkAt s n hs).frobeniusEnd = ψ (-d) := by
  subst ht
  obtain ⟨h₁, h₂⟩ := affineLine.frobeniusEnd_stalkAt_artinSchreierImage ψ hn t d hX hs
  rw [h₁, map_smul, LinearMap.trace_id, h₂, Nat.cast_one, smul_eq_mul, mul_one]

end Trivialization


section Points

omit [Finite k₀]

/-- The coordinate of a point `f : Spec Ω ⟶ 𝔸¹_{k₀}` with values in a ring. -/
noncomputable def affineLine.pointCoord {Ω : Type u} [CommRing Ω]
    (f : Spec (.of Ω) ⟶ affineLine k₀) : Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom (f.appTop (AffineSpace.coord _ PUnit.unit))

/-- The coordinate of the composite of a point with `Spec φ` is the image under `φ`. -/
lemma affineLine.pointCoord_specMap_comp {Ω Ω' : Type u} [CommRing Ω] [CommRing Ω']
    (φ : Ω →+* Ω') (f : Spec (.of Ω) ⟶ affineLine k₀) :
    affineLine.pointCoord (Spec.map (CommRingCat.ofHom φ) ≫ f) = φ (affineLine.pointCoord f) := by
  rw [affineLine.pointCoord, affineLine.pointCoord, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

/-- The image of a global function on `Spec k₀` under a point over `k₀` is its image in `Ω`. -/
lemma affineLine.appTop_structure_apply {Ω : Type u} [CommRing Ω] [Algebra k₀ Ω]
    (f : Spec (.of Ω) ⟶ affineLine k₀)
    (hf : f ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ Ω))) (c : k₀) :
    (Scheme.ΓSpecIso (.of Ω)).hom.hom (f.appTop ((affineLine k₀ ↘
      Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom c))) =
      algebraMap k₀ Ω c := by
  rw [← CommRingCat.comp_apply ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).appTop) f.appTop,
    ← Scheme.Hom.comp_appTop, hf, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

/-- The coordinate of a translate. -/
lemma affineLine.pointCoord_comp_translation {Ω : Type u} [CommRing Ω] [Algebra k₀ Ω]
    (f : Spec (.of Ω) ⟶ affineLine k₀)
    (hf : f ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ Ω))) (c : k₀) :
    affineLine.pointCoord (f ≫ affineLine.translation k₀ c) =
      affineLine.pointCoord f + algebraMap k₀ Ω c := by
  rw [affineLine.pointCoord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineLine.translation, AffineSpace.translation_appTop_coord, map_add, map_add,
    affineLine.appTop_structure_apply f hf]
  rfl

/-- The coordinate of a multiple. -/
lemma affineLine.pointCoord_comp_smul {Ω : Type u} [CommRing Ω] [Algebra k₀ Ω]
    (f : Spec (.of Ω) ⟶ affineLine k₀)
    (hf : f ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ Ω))) (a : k₀) :
    affineLine.pointCoord (f ≫ affineLine.smul k₀ a) =
      algebraMap k₀ Ω a * affineLine.pointCoord f := by
  rw [affineLine.pointCoord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineLine.smul, AffineSpace.smul_appTop_coord, map_mul, map_mul,
    affineLine.appTop_structure_apply f hf]
  rfl

variable [Finite k₀] in
/-- The coordinate of the image under the Artin–Schreier map. -/
lemma affineLine.pointCoord_comp_artinSchreierMap {Ω : Type u} [CommRing Ω]
    (f : Spec (.of Ω) ⟶ affineLine k₀) :
    affineLine.pointCoord (f ≫ affineLine.artinSchreierMap k₀) =
      affineLine.pointCoord f ^ Nat.card k₀ - affineLine.pointCoord f := by
  let := Fintype.ofFinite k₀
  rw [affineLine.pointCoord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineLine.artinSchreierMap, AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_sub,
    map_pow, map_pow, Nat.card_eq_fintype_card]
  rfl

variable [Finite k₀] in
/-- If `y ^ q - y = w` in `k̄` and `∑_{i < n} w ^ (q ^ i) = c ∈ k₀`, then the `n`-th power of the
geometric Frobenius maps `y` to `y - c`: the arithmetic Frobenius maps `y ^ (q ^ i)` to
`y ^ (q ^ (i + 1)) = y ^ (q ^ i) + w ^ (q ^ i)`, so `y ^ (q ^ n) = y + c`. -/
lemma geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_sub_eq {n : ℕ}
    {y w : AlgebraicClosure k₀} (h : y ^ Nat.card k₀ - y = w) {c : k₀}
    (hw : ∑ i ∈ Finset.range n, w ^ (Nat.card k₀ ^ i) = algebraMap k₀ (AlgebraicClosure k₀) c) :
    letI := Fintype.ofFinite k₀
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀) ^ n) y =
      y - algebraMap k₀ (AlgebraicClosure k₀) c := by
  let := Fintype.ofFinite k₀
  set F := FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)
  have hF (z : AlgebraicClosure k₀) : F z = z ^ Nat.card k₀ := by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]
  have key (m : ℕ) : (F ^ m) y = y + ∑ i ∈ Finset.range m, w ^ (Nat.card k₀ ^ i) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, map_sum, Finset.sum_range_succ', pow_zero,
        pow_one, hF, ← h]
      simp only [hF, ← pow_mul, ← pow_succ]
      ring
  have e := congrArg (fun z ↦ (F ^ n).symm z) (key n)
  simp only [hw, AlgEquiv.symm_apply_apply, map_add, AlgEquiv.commutes] at e
  rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv]
  exact eq_sub_of_add_eq e.symm

/-- The sum `∑_{i < n} z ^ (q ^ i)` of the conjugates of an element of a field with `qⁿ` elements
is its trace, embedded into `k̄`. -/
lemma sum_pow_eq_algebraMap_trace {K : Type u} [Field K] [Algebra k₀ K] [Finite K] {n : ℕ}
    (hK : Module.finrank k₀ K = n) (ι : K →ₐ[k₀] AlgebraicClosure k₀) (z : K) :
    ∑ i ∈ Finset.range n, ι z ^ (Nat.card k₀ ^ i) =
      algebraMap k₀ (AlgebraicClosure k₀) (Algebra.trace k₀ K z) := by
  rw [← ι.commutes, FiniteField.algebraMap_trace_eq_sum_pow, map_sum, hK]
  simp only [map_pow]

variable [Finite k₀] in
/-- **The Frobenius on the fibre of the Artin–Schreier cover.** Let `x` be an `𝔽_{qⁿ}`-rational
point of the affine line with coordinate `z`, and `s` the geometric point over `x` for an embedding
`ι : 𝔽_{qⁿ} ↪ k̄`. Then `s` lifts along `ĀS` to a geometric point `t`, given by a root `y` of
`y ^ q - y = ι z`, and the two lifts `σⁿ ∘ t` and `Frⁿ ∘ t` of `σⁿ ∘ s = Frⁿ ∘ s` differ by the
translation by `Tr_{𝔽_{qⁿ}/k₀}(z)`: the geometric Frobenius maps `y` to `y - Tr(z)`, since
`y ^ (q ^ n) = y + Tr(z)`. -/
theorem affineLine.exists_comp_geometricArtinSchreierMap_eq {n : ℕ} (hn : n ≠ 0)
    (ι : FiniteField.galoisExtension k₀ n →ₐ[k₀] AlgebraicClosure k₀)
    (x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
    ∃ t : Spec (.of (AlgebraicClosure k₀)) ⟶
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      t ≫ ĀS = (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint ι x.1 x.2 ∧
      (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ t =
        (t ≫ (affineLine.geometricTranslationIso k₀
          (-Algebra.trace k₀ _ (affineLine.pointCoord x.1))).hom) ≫
          ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  let := Fintype.ofFinite k₀
  set s := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint ι x.1 x.2
  obtain ⟨t₀, ht₀⟩ := AffineSpace.exists_comp_artinSchreierMap_eq k₀
    (s ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
  have ht₀' : t₀ ≫ affineLine.artinSchreierMap k₀ =
      s ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj := ht₀
  have hstr : t₀ ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀))) := by
    rw [← comp_over (affineLine.artinSchreierMap k₀) (Spec (CommRingCat.of k₀)),
      reassoc_of% ht₀', Scheme.Hom.geometricFiber_condition,
      Scheme.Hom.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure_assoc]
    rfl
  let t : Spec (.of (AlgebraicClosure k₀)) ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    pullback.lift t₀ (𝟙 _) (by rw [hstr, Category.id_comp]; rfl)
  have htp : t ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj = t₀ :=
    pullback.lift_fst _ _ _
  have hta : t ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      𝟙 _ :=
    pullback.lift_snd _ _ _
  -- the coordinate `y` of `t` is a root of `y ^ q - y = ι z`
  have hy : affineLine.pointCoord t₀ ^ Nat.card k₀ - affineLine.pointCoord t₀ =
      ι (affineLine.pointCoord x.1) := by
    rw [← affineLine.pointCoord_comp_artinSchreierMap, ht₀',
      Scheme.Hom.geometricFiberPoint_comp_geometricFiberProj]
    exact affineLine.pointCoord_specMap_comp ι.toRingHom x.1
  have hφ := geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_sub_eq hy
    (sum_pow_eq_algebraMap_trace (FiniteField.finrank_galoisExtension k₀ n hn) ι _)
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).hom.hom :=
    fun a b h ↦ by simpa using congrArg (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom h
  have h₀ : (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ t₀ =
      t₀ ≫ affineLine.translation k₀ (-Algebra.trace k₀ _ (affineLine.pointCoord x.1)) := by
    refine AffineSpace.hom_ext ?_ fun _ ↦ hinj ?_
    · rw [Category.assoc, hstr, Category.assoc, comp_over, hstr, specGeometricFrobenius_pow_hom,
        ← Spec.map_comp]
      congr 1
      ext a
      simp
    · rw [specGeometricFrobenius_pow_hom]
      refine (affineLine.pointCoord_specMap_comp _ t₀).trans ?_
      refine Eq.trans ?_ (affineLine.pointCoord_comp_translation t₀ hstr _).symm
      rw [map_neg, ← sub_eq_add_neg, ← hφ]
      rfl
  refine ⟨t, Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_, Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_⟩
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, reassoc_of% htp, ht₀']
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure, hta,
      Scheme.Hom.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure]
  · rw [Category.assoc, htp, Category.assoc, Category.assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj,
      affineLine.geometricTranslationIso, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      reassoc_of% htp, h₀]
  · rw [Category.assoc, hta, Category.assoc, Category.assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      affineLine.geometricTranslationIso,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure_assoc, reassoc_of% hta,
      Category.comp_id]

end Points

/-- **Trace function of the Artin–Schreier sheaf.** For an additive character `ψ` of `k₀`,
`a ∈ k₀` and `n ≠ 0`, the trace function of `ℒ_{ψ(a x)}` at an `𝔽_{qⁿ}`-rational point `x` of
the affine line is `ψ(Tr_{𝔽_{qⁿ}/k₀}(a x))`, for the local geometric Frobenius.
(blueprint: `lemma-artin-schreier-character-sheaf--6`) -/
theorem WeilSheaf.traceFunction_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) {n : ℕ}
    (hn : n ≠ 0)
    (x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
    (artinSchreier ψ a).traceFunction n x =
      ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
        (algebraMap k₀ _ a * (Scheme.ΓSpecIso (.of _)).hom.hom
          (x.1.appTop (AffineSpace.coord _ PUnit.unit)))) :=
  by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  rw [artinSchreier, WeilSheaf.traceFunction_upperStar, WeilSheaf.traceFunction]
  -- the Frobenius acts on the fibre `{y : y ^ q - y = a x}` of the Artin–Schreier covering
  -- over the geometric point above `x` as the translation by `Tr(a x)`
  obtain ⟨t, ht, hX⟩ := affineLine.exists_comp_geometricArtinSchreierMap_eq hn IsAlgClosed.lift
    ((affineLine.smul k₀ a).mapFieldPoints _ x)
  rw [affineLine.trace_frobeniusEnd_stalkAt_artinSchreierImage ψ (Nat.one_le_iff_ne_zero.2 hn) _ t
    ht _ hX, neg_neg, Scheme.Hom.mapFieldPoints_coe, affineLine.pointCoord_comp_smul x.1 x.2]
  rfl

end AlgebraicGeometry
