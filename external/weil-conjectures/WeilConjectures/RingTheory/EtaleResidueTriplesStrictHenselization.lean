/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.RingTheory.IsStrictHenselization

/-!
# Comparison of the two pointed étale colimit presentations

Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private abbrev PointedEtale (R : CommRingCat.{u}) (K : Type u) [Field K]
    [Algebra R K] :=
  ObjectProperty.FullSubcategory
    (fun X : Over (CommAlgCat.of R K) ↦ Algebra.Etale R X.left)

private noncomputable def tripleAsPointed
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K] [Algebra R K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K))
    (t : EtaleResidueTriples R p K χ) : PointedEtale R K := by
  let : Algebra R t.B := t.α.hom.toAlgebra
  have ht : Algebra.Etale R t.B := by
    have := t.etale
    exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp inferInstance
  let b : t.B →ₐ[R] K :=
    { __ := ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom
      commutes' := fun r ↦ by
        exact congrArg (fun f : R ⟶ CommRingCat.of K ↦ f.hom r)
          (t.compatible.trans hχ) }
  exact ⟨Over.mk (CommAlgCat.ofHom b), ht⟩

private noncomputable def pointedAsTriple
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K] [Algebra R K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K))
    (X : PointedEtale R K) : EtaleResidueTriples R p K χ := by
  let B := CommRingCat.of X.obj.left
  let b : B ⟶ CommRingCat.of K := CommRingCat.ofHom X.obj.hom.hom.toRingHom
  let z := SpecToEquivOfField K (Spec B) (Spec.map b)
  have hz : (ΓSpecIso B).inv ≫ (Spec B).Γevaluation z.1 ≫ z.2 = b := by
    apply Spec.map_injective
    rw [show Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation z.1 ≫ z.2) =
      Spec.map z.2 ≫ (Spec B).fromSpecResidueField z.1 by
        simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
        rfl]
    exact (SpecToEquivOfField K (Spec B)).symm_apply_apply (Spec.map b)
  have hw : CommRingCat.ofHom (algebraMap R X.obj.left) ≫ b =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
    rw [hχ]
    ext r
    exact X.obj.hom.hom.commutes r
  refine ⟨B, CommRingCat.ofHom (algebraMap R X.obj.left), ?_, z.1, ?_, z.2, ?_⟩
  · have := X.property
    exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  · have h : (Spec.map z.2 ≫ (Spec B).fromSpecResidueField z.1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R X.obj.left)) =
        Spec.map χ ≫ (Spec R).fromSpecResidueField p := by
      rw [← show Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation z.1 ≫ z.2) =
          Spec.map z.2 ≫ (Spec B).fromSpecResidueField z.1 by
            simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
            rfl,
        ← show Spec.map ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) =
          Spec.map χ ≫ (Spec R).fromSpecResidueField p by
            simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
            rfl,
        ← Spec.map_comp, hz]
      exact congrArg Spec.map hw
    have h' := congrArg (fun f : Spec (CommRingCat.of K) ⟶ Spec R ↦
      f (IsLocalRing.closedPoint K)) h
    simpa using h'
  · rw [hz]
    exact hw

private lemma pointedAsTriple_point
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K] [Algebra R K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K))
    (X : PointedEtale R K) :
    let t := pointedAsTriple R p K χ hχ X
    (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      CommRingCat.ofHom X.obj.hom.hom.toRingHom := by
  apply Spec.map_injective
  rw [show Spec.map ((ΓSpecIso (pointedAsTriple R p K χ hχ X).B).inv ≫
        (Spec (pointedAsTriple R p K χ hχ X).B).Γevaluation
          (pointedAsTriple R p K χ hχ X).q ≫ (pointedAsTriple R p K χ hχ X).φ) =
      Spec.map (pointedAsTriple R p K χ hχ X).φ ≫
        (Spec (pointedAsTriple R p K χ hχ X).B).fromSpecResidueField
          (pointedAsTriple R p K χ hχ X).q by
        simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
        rfl]
  exact (SpecToEquivOfField K (Spec (.of X.obj.left))).symm_apply_apply
    (Spec.map (CommRingCat.ofHom X.obj.hom.hom.toRingHom))

private noncomputable def tripleHom {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    {s t : EtaleResidueTriples R p K χ} (f : s.B ⟶ t.B) (ha : s.α ≫ f = t.α)
    (hb : f ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) : s ⟶ t :=
  InducedCategory.homMk (Under.homMk (Over.homMk f hb) (by
    apply Over.OverMorphism.ext
    exact ha))

/-- A colimit of residue triples is a strict henselization in the pointed algebra
presentation. Source: Stacks Project, Tag 04GW (lemma-strict-henselization-different).
(blueprint: lem-sc-etale-triples-colimit-is-strict-henselization).

Proof: An étale algebra equipped with a map to `K` determines a unique prime and
residue embedding, by the equivalence between maps from `Spec K` and residue-field
points. Conversely a residue triple determines the map to `K` by evaluation. The
compatibility equation is precisely the algebra-map equation over `R`, and the
morphisms on both sides are the ring maps commuting with `R` and `K`. Transport
the universal ring cocone along this equivalence. Its legs are algebra maps by `hρ`.
The descended ring map to any algebra cocone respects `R`, as checked on the identity
triple. Thus the transported cocone is universal in `CommAlgCat R`, has vertex `c.pt`,
and witnesses `IsStrictHenselization`. No Noetherianity or completion is involved. -/
theorem etaleResidueTriples_colimit_isStrictHenselization
    (R : CommRingCat.{u}) [IsLocalRing R] (p : Spec R)
    (K : Type u) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (hχ : (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ =
      CommRingCat.ofHom (algebraMap R K))
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) (hc : IsColimit c)
    [Algebra R c.pt]
    (hρ : ∀ t, t.α ≫ c.ι.app t = CommRingCat.ofHom (algebraMap R c.pt)) :
    Algebra.IsStrictHenselization R K c.pt := by
  classical
  let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Algebra.Etale R X.left
  let D := P.ι ⋙ Over.forget (CommAlgCat.of R K)
  let s := pointedAsTriple R p K χ hχ
  let F := tripleAsPointed R p K χ hχ
  have hs (X : PointedEtale R K) :
      (ΓSpecIso (s X).B).inv ≫ (Spec (s X).B).Γevaluation (s X).q ≫ (s X).φ =
        CommRingCat.ofHom X.obj.hom.hom.toRingHom :=
    pointedAsTriple_point R p K χ hχ X
  let d : Cocone D :=
    { pt := CommAlgCat.of R c.pt
      ι :=
        { app := fun X ↦ CommAlgCat.ofHom
            { __ := (c.ι.app (s X)).hom
              commutes' := fun r ↦
                congrArg (fun f : R ⟶ c.pt ↦ f.hom r) (hρ (s X)) }
          naturality := fun X Y f ↦ by
            let g : s X ⟶ s Y := tripleHom
              (CommRingCat.ofHom f.hom.left.hom.toRingHom) (by
                ext r
                exact f.hom.left.hom.commutes r) (by
                rw [hs, hs]
                exact congrArg (fun h ↦ CommRingCat.ofHom h.hom.toRingHom) (Over.w f.hom))
            ext x
            exact congrArg (fun h ↦ h.hom x) (c.w g) } }
  let k' (k : Cocone D) : Cocone (etaleResidueTriplesRingDiagram R p K χ) :=
    { pt := CommRingCat.of k.pt
      ι :=
        { app := fun t ↦ CommRingCat.ofHom (k.ι.app (F t)).hom.toRingHom
          naturality := fun t v f ↦ by
            let : Algebra R t.B := t.α.hom.toAlgebra
            let : Algebra R v.B := v.α.hom.toAlgebra
            let g : F t ⟶ F v := ObjectProperty.homMk
              (Over.homMk (CommAlgCat.ofHom
                { __ := f.hom.right.left.hom
                  commutes' := fun r ↦
                    congrArg (fun h : R ⟶ v.B ↦ h.hom r)
                      (congrArg CommaMorphism.left (Under.w f.hom)) }) (by
                apply CommAlgCat.hom_ext
                apply AlgHom.ext
                intro x
                exact congrArg (fun h ↦ h.hom x) (Over.w f.hom.right)))
            ext x
            exact congrArg (fun h ↦ h.hom x) (k.w g) } }
  let desc (k : Cocone D) : d.pt ⟶ k.pt := by
    refine CommAlgCat.ofHom { __ := (hc.desc (k' k)).hom, commutes' := ?_ }
    intro r
    let t0 : EtaleResidueTriples R p K χ :=
      ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
    have ht0 : c.ι.app t0 = CommRingCat.ofHom (algebraMap R c.pt) := by
      simpa [t0] using hρ t0
    have h := hc.fac (k' k) t0
    rw [ht0] at h
    exact (congrArg (fun f ↦ f.hom r) h).trans ((k.ι.app (F t0)).hom.commutes r)
  have hd : IsColimit d := by
    refine { desc := desc, fac := ?_, uniq := ?_ }
    · intro k X
      let : Algebra R (s X).B := (s X).α.hom.toAlgebra
      let g : F (s X) ⟶ X := ObjectProperty.homMk
        (Over.homMk (CommAlgCat.ofHom
          { __ := RingHom.id X.obj.left
            commutes' := fun r ↦ rfl }) (by
          apply CommAlgCat.hom_ext
          apply AlgHom.ext
          intro x
          exact (congrArg (fun h ↦ h.hom x) (hs X)).symm))
      ext x
      have h := congrArg (fun f ↦ f.hom x) (hc.fac (k' k) (s X))
      change (hc.desc (k' k)).hom ((c.ι.app (s X)).hom x) = (k.ι.app X).hom x
      change (hc.desc (k' k)).hom ((c.ι.app (s X)).hom x) =
        (k.ι.app (F (s X))).hom x at h
      exact h.trans (congrArg (fun f ↦ f.hom x) (k.w g)).symm
    · intro k m hm
      apply CommAlgCat.hom_ext
      apply AlgHom.toRingHom_injective
      change m.hom.toRingHom = (hc.desc (k' k)).hom
      suffices h : CommRingCat.ofHom m.hom.toRingHom = hc.desc (k' k) from
        congrArg CommRingCat.Hom.hom h
      apply hc.hom_ext
      intro t
      let g : t ⟶ s (F t) := tripleHom (CommRingCat.ofHom (RingHom.id t.B)) (by
        ext r
        rfl) (by
        rw [hs]
        rfl)
      have hleg : c.ι.app (s (F t)) = c.ι.app t := by
        have h := c.w g
        change (𝟙 t.B) ≫ c.ι.app (s (F t)) = c.ι.app t at h
        simpa only [Category.id_comp] using h
      ext x
      have h := congrArg (fun f ↦ f.hom x) (hm (F t))
      change m.hom ((c.ι.app (s (F t))).hom x) = (k.ι.app (F t)).hom x at h
      rw [hleg] at h
      exact h.trans (congrArg (fun f ↦ f.hom x) (hc.fac (k' k) t)).symm
  exact ⟨d, ⟨hd⟩, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.Scheme
