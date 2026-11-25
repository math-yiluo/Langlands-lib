/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Pullbacks of Artin–Schreier sheaves

The pullback of the Artin–Schreier sheaf `ℒ_ψ` along the Artin–Schreier map `AS` is the constant
Weil sheaf (`AlgebraicGeometry.WeilSheaf.upperStarArtinSchreierMapImageIso`): the adjoint
`AS^* ℒ_ψ ⟶ ℚ̄_ℓ` of the inclusion `ℒ_ψ ⟶ AS_* ℚ̄_ℓ` is a morphism of Weil sheaves whose underlying
morphism is the geometric trivialisation of `ĀS^* ℒ_ψ`. Hence the pullback of `ℒ_ψ` along any
`φ` with `φ ≫ AS = φ` is constant; in particular `ℒ_{ψ(0 x)} ≅ ℚ̄_ℓ`
(`AlgebraicGeometry.nonempty_artinSchreier_zero_iso_adicConstant`, blueprint
`lemma-artin-schreier-character-sheaf`).

## Implementation notes

Declarations mentioning `AS_*` or `image e_ψ` with instance arguments found inline (e.g.
`QuasiCompact AS` through `IsFinite AS`) make the kernel re-check these instance terms, which
times out. The instances are therefore given names (and a high local priority) below.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀]

/-- The scaling by `1` of the affine line is the identity. -/
lemma affineLine.smul_one : affineLine.smul k₀ 1 = 𝟙 _ :=
  AffineSpace.hom_ext (by simp [affineLine.smul]) fun _ ↦ by simp [affineLine.smul]

/-- Scaling by `a b` is scaling by `a` followed by scaling by `b`. -/
lemma affineLine.smul_mul (a b : k₀) :
    affineLine.smul k₀ (a * b) = affineLine.smul k₀ a ≫ affineLine.smul k₀ b := by
  refine AffineSpace.hom_ext (by simp [affineLine.smul]) fun _ ↦ ?_
  simp only [affineLine.smul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.smul_appTop_coord, map_mul]
  rw [← CommRingCat.comp_apply (affineLine k₀ ↘ Spec (.of k₀)).appTop, ← Scheme.Hom.comp_appTop,
    AffineSpace.smul_over]
  ring

variable [Finite k₀]

/-- The scaling by `0` is fixed by the Artin–Schreier map: `AS(0 · x) = 0`. -/
lemma affineLine.smul_zero_comp_artinSchreierMap :
    affineLine.smul k₀ 0 ≫ affineLine.artinSchreierMap k₀ = affineLine.smul k₀ 0 := by
  let := Fintype.ofFinite k₀
  refine AffineSpace.hom_ext (by simp [affineLine.smul, affineLine.artinSchreierMap]) fun _ ↦ ?_
  simp only [affineLine.smul, affineLine.artinSchreierMap, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.smul_appTop_coord,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow, map_zero, zero_mul]
  simp [Fintype.card_ne_zero]

/-- The Artin–Schreier map is quasi-compact (named, see the implementation notes). -/
theorem affineLine.quasiCompact_artinSchreierMap :
    QuasiCompact (affineLine.artinSchreierMap k₀) := inferInstance

/-- The Artin–Schreier map is quasi-separated (named, see the implementation notes). -/
theorem affineLine.quasiSeparated_artinSchreierMap :
    QuasiSeparated (affineLine.artinSchreierMap k₀) := inferInstance

/-- The Artin–Schreier map is locally of finite type (named, see the implementation notes). -/
theorem affineLine.locallyOfFiniteType_artinSchreierMap :
    LocallyOfFiniteType (affineLine.artinSchreierMap k₀) := inferInstance

omit [Finite k₀] in
/-- The affine line is locally of finite type over `k₀` (named, see the implementation notes). -/
theorem affineLine.locallyOfFiniteType_over :
    LocallyOfFiniteType (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := inferInstance

end AffineLine

attribute [local instance high] affineLine.quasiCompact_artinSchreierMap
  affineLine.quasiSeparated_artinSchreierMap affineLine.locallyOfFiniteType_artinSchreierMap
  affineLine.locallyOfFiniteType_over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section UpperStarLift

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The morphism `φ^* P ⟶ F` of Weil sheaves adjoint to `f : P ⟶ φ_* F` under `φ^* ⊣ φ_*`. -/
noncomputable def WeilSheaf.upperStarLift {P : WeilSheaf k₀ l Y} {F : WeilSheaf k₀ l X}
    (f : P ⟶ (WeilSheaf.lowerStar φ).obj F) : (WeilSheaf.upperStar φ).obj P ⟶ F :=
  ((WeilSheaf.upperStarLowerStarAdjunction φ).homEquiv P F).symm f

/-- The underlying morphism of `AlgebraicGeometry.WeilSheaf.upperStarLift`: `φ̄^*` of the
underlying morphism followed by the counit of `φ̄^* ⊣ φ̄_*`. -/
lemma WeilSheaf.upperStarLift_hom_hom_f {P : WeilSheaf k₀ l Y} {F : WeilSheaf k₀ l X}
    (f : P ⟶ (WeilSheaf.lowerStar φ).obj F) :
    (WeilSheaf.upperStarLift φ f).hom.hom.f =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l].map f.hom.hom.f ≫
        (ProEtale.adicUpperStarLowerStarAdjunction l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app F.obj.carrier :=
  rfl

end UpperStarLift

/-- The image of the projector `e_ψ` exists (named, see the implementation notes). -/
theorem WeilSheaf.hasImage_artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l)) :
    HasImage (WeilSheaf.artinSchreierIdempotent ψ) := inferInstance

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

/-- The image of `e_ψ` does not depend on the proof that it exists. Rewriting with this equation
replaces the instance found elsewhere by the named one: the kernel would otherwise compare
`F.obj (image e_ψ)` for two instances by unfolding the functor `F`. -/
theorem WeilSheaf.image_artinSchreierIdempotent_eq (ψ : AddChar k₀ (PadicAlgCl l))
    {h : HasImage (WeilSheaf.artinSchreierIdempotent ψ)} :
    @image _ _ _ _ (WeilSheaf.artinSchreierIdempotent ψ) h =
      @image _ _ _ _ (WeilSheaf.artinSchreierIdempotent ψ)
        (WeilSheaf.hasImage_artinSchreierIdempotent ψ) :=
  rfl

section Trivialization

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

variable (ψ : AddChar k₀ (PadicAlgCl l))

variable (l) in
/-- The evaluation `ĀS^* ℒ_ψ ⟶ ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` at the point of the fibre given by the
Artin–Schreier cover, as a morphism of sheaves of modules. -/
noncomputable def affineLine.artinSchreierImageEvalModHom :
    (ĀS)^*ᵃ[l].obj (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier ⟶
      (WeilSheaf.adicConstant k₀ l (affineLine k₀)).obj.carrier :=
  (ĀS)^*ᵃ[l].map (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f ≫
    (ProEtale.adicUpperStarLowerStarAdjunction l ĀS).counit.app _

lemma affineLine.artinSchreierImageEvalModHom_hom :
    (affineLine.artinSchreierImageEvalModHom l ψ).hom =
      affineLine.artinSchreierImageEval ψ 0 := by
  rw [affineLine.artinSchreierImageEvalModHom, Mod.comp_hom', ProEtale.adicUpperStar_map_hom]
  erw [Adjunction.modAdjunction_counit_app_hom]
  rw [affineLine.artinSchreierImageEval, affineLine.artinSchreierTranslation_zero,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

lemma affineLine.isIso_artinSchreierImageEval :
    IsIso (affineLine.artinSchreierImageEval ψ 0) := by
  obtain ⟨E, hE⟩ := affineLine.exists_iso_artinSchreierImage ψ
  have h := hE 0
  rw [AddChar.map_zero_eq_one] at h
  have h' : affineLine.artinSchreierImageEval ψ 0 = E.hom := by
    rw [affineLine.artinSchreierImageEval, h]
    erw [one_smul]
    exact Category.comp_id _
  rw [h']
  infer_instance

instance : IsIso (affineLine.artinSchreierImageEvalModHom l ψ) := by
  have : IsIso (affineLine.artinSchreierImageEvalModHom l ψ).hom := by
    rw [affineLine.artinSchreierImageEvalModHom_hom]
    exact affineLine.isIso_artinSchreierImageEval ψ
  have : IsIso ((Mod.forget _).map (affineLine.artinSchreierImageEvalModHom l ψ)) :=
    inferInstanceAs (IsIso (affineLine.artinSchreierImageEvalModHom l ψ).hom)
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- The trivialisation `AS^* ℒ_ψ ⟶ ℚ̄_ℓ` of the pullback of `ℒ_ψ` along the Artin–Schreier map,
as a morphism of Weil sheaves: the adjoint of the inclusion `ℒ_ψ ⟶ AS_* ℚ̄_ℓ` under
`AS^* ⊣ AS_*`, the evaluation at the point of the fibre given by the cover. -/
noncomputable def WeilSheaf.upperStarArtinSchreierMapImageHom :
    (WeilSheaf.upperStar (affineLine.artinSchreierMap k₀)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)) ⟶
      WeilSheaf.adicConstant k₀ l (affineLine k₀) :=
  WeilSheaf.upperStarLift _ (image.ι (WeilSheaf.artinSchreierIdempotent ψ))

lemma WeilSheaf.upperStarArtinSchreierMapImageHom_hom_hom_f :
    (WeilSheaf.upperStarArtinSchreierMapImageHom ψ).hom.hom.f =
      affineLine.artinSchreierImageEvalModHom l ψ := by
  rw [WeilSheaf.upperStarArtinSchreierMapImageHom, WeilSheaf.upperStarLift_hom_hom_f]
  rfl

instance : IsIso (WeilSheaf.upperStarArtinSchreierMapImageHom ψ) := by
  have : IsIso (WeilSheaf.upperStarArtinSchreierMapImageHom ψ).hom.hom.f := by
    rw [WeilSheaf.upperStarArtinSchreierMapImageHom_hom_hom_f]
    infer_instance
  exact WeilSheaf.isIso_of_isIso_hom_hom_f _

/-- Blueprint `lemma-artin-schreier-character-sheaf`: the pullback of `ℒ_ψ` along the Artin–Schreier
map is the constant Weil sheaf, `AS^* ℒ_ψ ≅ ℚ̄_ℓ`. -/
noncomputable def WeilSheaf.upperStarArtinSchreierMapImageIso :
    (WeilSheaf.upperStar (affineLine.artinSchreierMap k₀)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)) ≅
      WeilSheaf.adicConstant k₀ l (affineLine k₀) :=
  asIso (WeilSheaf.upperStarArtinSchreierMapImageHom ψ)

/-- Blueprint `lemma-artin-schreier-character-sheaf`: if `AS^* L ≅ ℚ̄_ℓ` (e.g. `L = ℒ_ψ`), the
pullback of `L` along a morphism `φ : X ⟶ 𝔸¹` with `AS ∘ φ = φ` is constant,
`φ^* L ≅ φ^* AS^* L ≅ φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
theorem WeilSheaf.nonempty_iso_upperStar_of_comp_artinSchreierMap {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ affineLine k₀)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (h : φ ≫ affineLine.artinSchreierMap k₀ = φ)
    (L : WeilSheaf k₀ l (affineLine k₀))
    (e : (WeilSheaf.upperStar (affineLine.artinSchreierMap k₀)).obj L ≅
      WeilSheaf.adicConstant k₀ l (affineLine k₀)) :
    Nonempty ((WeilSheaf.upperStar φ).obj L ≅ WeilSheaf.adicConstant k₀ l X) := by
  obtain ⟨e'⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj φ
    (affineLine.artinSchreierMap k₀) φ h L
  exact ⟨e'.symm ≪≫ (WeilSheaf.upperStar φ).mapIso e ≪≫ WeilSheaf.upperStarAdicConstantIso φ⟩

/-- A variant of
`AlgebraicGeometry.WeilSheaf.nonempty_iso_upperStar_of_comp_artinSchreierMap` for an iterated
pullback: `φ^* g^* L ≅ ℚ̄_ℓ` if `φ ≫ g = g'` and `AS ∘ g' = g'`. -/
theorem WeilSheaf.nonempty_iso_upperStar_upperStar_of_comp_artinSchreierMap {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    (g : Y ⟶ affineLine k₀) (g' : X ⟶ affineLine k₀) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
    (h : φ ≫ g = g') (h' : g' ≫ affineLine.artinSchreierMap k₀ = g')
    (L : WeilSheaf k₀ l (affineLine k₀))
    (e : (WeilSheaf.upperStar (affineLine.artinSchreierMap k₀)).obj L ≅
      WeilSheaf.adicConstant k₀ l (affineLine k₀)) :
    Nonempty ((WeilSheaf.upperStar φ).obj ((WeilSheaf.upperStar g).obj L) ≅
      WeilSheaf.adicConstant k₀ l X) := by
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj φ g g' h L
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_iso_upperStar_of_comp_artinSchreierMap g' h' L e
  exact ⟨e₁ ≪≫ e₂⟩

end Trivialization

/-- Blueprint `lemma-artin-schreier-character-sheaf` (the case `f = 0`): `ℒ_{ψ(0 x)} ≅ ℚ̄_ℓ`, as
`AS ∘ [0] = [0]`. -/
theorem nonempty_artinSchreier_zero_iso_adicConstant (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreier ψ 0 ≅ WeilSheaf.adicConstant k₀ l (affineLine k₀)) := by
  rw [artinSchreier, WeilSheaf.image_artinSchreierIdempotent_eq]
  exact WeilSheaf.nonempty_iso_upperStar_of_comp_artinSchreierMap _
    (affineLine.smul_zero_comp_artinSchreierMap k₀) _
    (WeilSheaf.upperStarArtinSchreierMapImageIso ψ)

end AlgebraicGeometry
