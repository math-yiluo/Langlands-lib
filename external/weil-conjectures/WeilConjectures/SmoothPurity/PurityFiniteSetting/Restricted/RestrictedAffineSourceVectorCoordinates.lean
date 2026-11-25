/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction

/-! # Vector coordinates for a section of an ordered affine tower -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem freeBundleCoordinates (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) :
    let F : B.Modules := SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))
    ∃ c : VectorBundleZeroSection.scheme B d F ≅ AffineSpace (ULift.{u} (Fin d)) B,
      c.hom ≫ (AffineSpace (ULift.{u} (Fin d)) B ↘ B) =
          VectorBundleZeroSection.π B d F ∧
      VectorBundleZeroSection.zero B d F ≫ c.hom =
        AffineSpace.zeroSection (ULift.{u} (Fin d)) B := by
  let F : B.Modules := SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))
  let E := VectorBundleZeroSection.scheme B d F
  let π := VectorBundleZeroSection.π B d F
  let z := VectorBundleZeroSection.zero B d F
  let U : E.Opens := π ⁻¹ᵁ (⊤ : B.Opens)
  let e := Scheme.Modules.restrictFreeIso (⊤ : B.Opens).ι (ULift.{u} (Fin d))
  let v := VectorBundleZeroSection.trivializationMap B d F ⊤ e
  have hv := VectorBundleZeroSection.trivializationMap_spec B d F ⊤ e
  have : IsIso v := hv.1
  let t : E ≅ U.toScheme := E.topIso.symm ≪≫ E.isoOfEq (by simp [U])
  let c := t ≪≫ asIso v ≪≫ asIso (AffineSpace.map (ULift.{u} (Fin d)) B.topIso.hom)
  have ht : t.hom ≫ U.ι = 𝟙 E := by
    simp only [t, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
  have hz : z ≫ t.hom = B.topIso.inv ≫ VectorBundleZeroSection.zeroRestricted B d F ⊤ := by
    apply (cancel_mono U.ι).mp
    calc
      (z ≫ t.hom) ≫ U.ι = z := by
        rw [Category.assoc, ht, Category.comp_id]
      _ = (B.topIso.inv ≫ VectorBundleZeroSection.zeroRestricted B d F ⊤) ≫ U.ι := by
        dsimp only [VectorBundleZeroSection.zeroRestricted]
        rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc]
        change z = (B.topIso.inv ≫ B.topIso.hom) ≫ z
        rw [B.topIso.inv_hom_id, Category.id_comp]
  refine ⟨c, ?_, ?_⟩
  · simp only [c, Iso.trans_hom, asIso_hom, Category.assoc, AffineSpace.map_over]
    rw [← Category.assoc v, hv.2.1]
    change t.hom ≫ (π ∣_ ⊤) ≫ (⊤ : B.Opens).ι = π
    rw [morphismRestrict_ι, ← Category.assoc, ht, Category.id_comp]
  · simp only [c, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc z, hz]
    rw [Category.assoc B.topIso.inv, ← Category.assoc
      (VectorBundleZeroSection.zeroRestricted B d F ⊤), hv.2.2,
      AffineSpace.zeroSection_comp_map, ← Category.assoc,
      B.topIso.inv_hom_id, Category.id_comp]

/-- A section of an ordered affine tower becomes the zero section of the free bundle.
Source: smooth-purity, Agreement on the model, subtraction of the diagonal section.
(blueprint: lem-pur-restricted-affine-source-vector-coordinates).

Proof: use the global frame of the free rank-d module. The given tower coordinates
identify the section with a vector a of global functions. Translation by -a sends
that section to zero, and translation by a is its inverse. Compose the inverse
translated coordinates with the free-bundle frame. Projection and section identities
follow by the affine-space universal property. The empty coordinate list and empty
base satisfy the same identities. -/
theorem affineTowerSection_vectorCoordinates (B : Scheme.{u}) [IsNoetherian B] (d : ℕ)
    {T : Scheme.{u}} (g : T ⟶ B) (s : B ⟶ T) (hs : s ≫ g = 𝟙 B)
    (r : T ≅ affineTraceTower B d) (hr : r.hom ≫ affineTraceProjection B d = g) :
    ∃ (F : B.Modules) (hF : F.IsFiniteLocallyFreeOfRank d),
      letI := hF
      ∃ (c : VectorBundleZeroSection.scheme B d F ≅ AffineSpace (ULift.{u} (Fin d)) B)
        (_wc : c.hom ≫ (AffineSpace (ULift.{u} (Fin d)) B ↘ B) =
          VectorBundleZeroSection.π B d F)
        (_zc : VectorBundleZeroSection.zero B d F ≫ c.hom =
          AffineSpace.zeroSection (ULift.{u} (Fin d)) B)
        (e : VectorBundleZeroSection.scheme B d F ≅ T),
        e.hom ≫ g = VectorBundleZeroSection.π B d F ∧
        VectorBundleZeroSection.zero B d F ≫ e.hom = s := by
  let F : B.Modules := SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))
  obtain ⟨c, hc, hz⟩ := freeBundleCoordinates B d
  let r' := r ≪≫ affineTraceAffineSpaceIso B d
  have hr' : r'.hom ≫ (AffineSpace (ULift.{u} (Fin d)) B ↘ B) = g := by
    simpa only [r', Iso.trans_hom, Category.assoc, affineTraceAffineSpaceIso,
      asIso_hom, affineTraceToAffineSpace, AffineSpace.homOfVector_over] using hr
  let a : ULift.{u} (Fin d) → Γ(B, ⊤) :=
    fun i ↦ (s ≫ r'.hom).appTop (AffineSpace.coord B i)
  let τ : AffineSpace (ULift.{u} (Fin d)) B ≅ AffineSpace (ULift.{u} (Fin d)) B :=
    { hom := AffineSpace.translation (-a)
      inv := AffineSpace.translation a
      hom_inv_id := by rw [← AffineSpace.translation_add]; simp
      inv_hom_id := by rw [← AffineSpace.translation_add]; simp }
  let k := r' ≪≫ τ
  have hk : k.hom ≫ (AffineSpace (ULift.{u} (Fin d)) B ↘ B) = g := by
    simpa only [k, Iso.trans_hom, Category.assoc, τ, AffineSpace.translation_over] using hr'
  have hsk : s ≫ k.hom = AffineSpace.zeroSection (ULift.{u} (Fin d)) B := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, hk, hs, AffineSpace.zeroSection_over]
    · intro i
      change (s ≫ r'.hom ≫ AffineSpace.translation (-a)).appTop
        (AffineSpace.coord B i) = _
      rw [← Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.translation_appTop_coord, map_add, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop]
      simp only [Category.assoc, hr', hs, Scheme.Hom.id_appTop,
        ConcreteCategory.id_apply, Pi.neg_apply, a, add_neg_cancel,
        AffineSpace.zeroSection_appTop_coord]
  refine ⟨F, inferInstance, c, hc, hz, c ≪≫ k.symm, ?_, ?_⟩
  · change c.hom ≫ k.inv ≫ g = _
    rw [← hk, Iso.inv_hom_id_assoc, hc]
  · apply (cancel_mono k.hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, hsk]
    exact hz

end WeilConjectures.PurityFiniteSetting
