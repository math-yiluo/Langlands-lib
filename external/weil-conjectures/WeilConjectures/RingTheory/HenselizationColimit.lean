/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.FilteredColimitHenselianPair
import WeilConjectures.RingTheory.HenselizationUniversalProperty

/-!
# Henselization of pairs commutes with filtered colimits

Source: Stacks Project, More on Algebra, Tags 0A04 and 0A02
(blueprint: lem-weil-pbc-henselization-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

private theorem henselian_map_equiv {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) [HenselianRing R I] (e : R ≃+* S) :
    HenselianRing S (I.map e.toRingHom) := by
  have hm (x : S) : x ∈ I.map e.toRingHom ↔ e.symm x ∈ I := by
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro ha
      exact ⟨e.symm x, ha, e.apply_symm_apply x⟩
  refine ⟨?_, ?_⟩
  · have h := Ideal.map_mono (f := e.toRingHom) (HenselianRing.jac (R := R) (I := I))
    rw [Ideal.map_jacobson_of_bijective (f := e.toRingHom) e.bijective,
      Ideal.map_bot] at h
    exact h
  · intro f hf a₀ hroot hunit
    let f' := f.map e.symm.toRingHom
    have heval (g : Polynomial S) (x : S) :
        (g.map e.symm.toRingHom).eval (e.symm x) = e.symm (g.eval x) :=
      Polynomial.eval_map_apply (p := g) e.symm.toRingHom x
    have hroot' : f'.eval (e.symm a₀) ∈ I := by
      rw [heval]
      exact (hm _).mp hroot
    have hmap : (I.map e.toRingHom).map e.symm.toRingHom ≤ I := by
      simp [Ideal.map_map]
    let q := Ideal.quotientMap I e.symm.toRingHom
      (Ideal.map_le_iff_le_comap.mp hmap)
    have hunit' : IsUnit (Ideal.Quotient.mk I (f'.derivative.eval (e.symm a₀))) := by
      have h := hunit.map q
      change IsUnit (Ideal.Quotient.mk I (e.symm (f.derivative.eval a₀))) at h
      rw [Polynomial.derivative_map, heval]
      exact h
    obtain ⟨a, ha, hdiff⟩ := HenselianRing.is_henselian f' (hf.map _) (e.symm a₀)
      hroot' hunit'
    refine ⟨e a, ?_, (hm _).mpr ?_⟩
    · have hv := heval f (e a)
      simp only [e.symm_apply_apply] at hv
      change f.eval (e a) = 0
      apply e.symm.injective
      rw [map_zero, ← hv]
      exact ha
    · simpa using hdiff

private theorem henselian_henselization (R B : CommRingCat.{u}) (J : Ideal R)
    (η : R ⟶ B)
    (hB : ∃ c : Cocone (ObjectProperty.ι
      (fun C : Under R ↦ AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
          Ideal.le_comap_map))),
      Nonempty (IsColimit c) ∧ ∃ e : c.pt.right ≅ B, c.pt.hom ≫ e.hom = η) :
    HenselianRing B (J.map η.hom) := by
  obtain ⟨c, ⟨hc⟩, e, he⟩ := hB
  obtain ⟨_, _, c₀, ⟨hc₀⟩, hH, _⟩ := pair_henselization R J
  have := hH
  let a := hc₀.coconePointUniqueUpToIso hc
  let b := (Under.forget R).mapIso a ≪≫ e
  have hb : c₀.pt.hom ≫ b.hom = η := by
    dsimp [b]
    rw [← Category.assoc, Under.w a.hom, he]
  have h := henselian_map_equiv (J.map c₀.pt.hom.hom) b.commRingCatIsoToRingEquiv
  have hid : (J.map c₀.pt.hom.hom).map b.hom.hom = J.map η.hom := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, hb]
  exact hid ▸ h

private theorem lift_henselization (R B A : CommRingCat.{u}) (J : Ideal R)
    (η : R ⟶ B)
    (hB : ∃ c : Cocone (ObjectProperty.ι
      (fun C : Under R ↦ AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
          Ideal.le_comap_map))),
      Nonempty (IsColimit c) ∧ ∃ e : c.pt.right ≅ B, c.pt.hom ≫ e.hom = η)
    (K : Ideal A) [HenselianRing A K] (φ : R ⟶ A) (hφ : J.map φ.hom ≤ K) :
    ∃ g : B ⟶ A, η ≫ g = φ ∧ (J.map η.hom).map g.hom ≤ K ∧
      ∀ g' : B ⟶ A, η ≫ g' = φ → g' = g := by
  obtain ⟨c, hc, e, he⟩ := hB
  obtain ⟨ψ, hψ, _, hu⟩ := henselization_universal_property R J c hc A K φ.hom hφ
  let g := e.inv ≫ CommRingCat.ofHom ψ
  have hg : η ≫ g = φ := by
    rw [← he]
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    exact CommRingCat.hom_ext hψ
  refine ⟨g, hg, ?_, ?_⟩
  · rw [Ideal.map_map, ← CommRingCat.hom_comp, hg]
    exact hφ
  · intro g' hg'
    have h' : (e.hom ≫ g').hom = ψ := by
      apply hu
      change (c.pt.hom ≫ e.hom ≫ g').hom = φ.hom
      rw [← Category.assoc, he, hg']
    have h'' : e.hom ≫ g' = CommRingCat.ofHom ψ := CommRingCat.hom_ext h'
    simpa [g] using congrArg (fun f => e.inv ≫ f) h''

/-- Clause (1): the unique lifted maps form a directed system of pairs.
Source: Stacks Project, Tag 0A02, functoriality of the left adjoint, used in Tag 0A04
(blueprint: lem-weil-pbc-henselization-colimit).

Proof: Each target henselization is henselian by lem-weil-pbc-pair-henselization.
Apply lem-weil-pbc-henselization-universal-property to the transition map followed by
its target structure map; extension of ideals gives preservation of the stage ideals.
Identity and composition both commute with the structure maps, so uniqueness gives the
identity and composition laws. This is step 1 of the node's proof. -/
theorem pairHenselization_transition_system
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (B : Λ → CommRingCat.{u}) (η : ∀ i : Λ, F.obj i ⟶ B i)
    (hB : ∀ i : Λ, ∃ c : Cocone (ObjectProperty.ι
        (fun C : Under (F.obj i) ↦
          AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
            Function.Bijective (Ideal.quotientMap ((J i).map C.hom.hom) C.hom.hom
              (Ideal.le_comap_map)))),
        Nonempty (IsColimit c) ∧ ∃ e : c.pt.right ≅ B i,
          c.pt.hom ≫ e.hom = η i) :
    ∃ t : ∀ {i j : Λ}, (i ⟶ j) → (B i ⟶ B j),
      (∀ {i j : Λ} (f : i ⟶ j),
        (η i ≫ t f = F.map f ≫ η j) ∧
        (∀ g : B i ⟶ B j, η i ≫ g = F.map f ≫ η j → g = t f) ∧
        Ideal.map (t f).hom ((J i).map (η i).hom) ≤ (J j).map (η j).hom) ∧
      (∀ i : Λ, t (𝟙 i) = 𝟙 (B i)) ∧
      (∀ {i j k : Λ} (f : i ⟶ j) (g : j ⟶ k), t (f ≫ g) = t f ≫ t g) := by
  classical
  have hH (j : Λ) : HenselianRing (B j) ((J j).map (η j).hom) :=
    henselian_henselization (F.obj j) (B j) (J j) (η j) (hB j)
  have lifts {i j : Λ} (f : i ⟶ j) :
      ∃ g : B i ⟶ B j, η i ≫ g = F.map f ≫ η j ∧
        ((J i).map (η i).hom).map g.hom ≤ (J j).map (η j).hom ∧
        ∀ g' : B i ⟶ B j, η i ≫ g' = F.map f ≫ η j → g' = g := by
    have := hH j
    apply lift_henselization (F.obj i) (B i) (B j) (J i) (η i) (hB i)
    rw [CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.map_mono (hJ f)
  let t : ∀ {i j : Λ}, (i ⟶ j) → (B i ⟶ B j) := fun {_ _} f => (lifts f).choose
  have ht {i j : Λ} (f : i ⟶ j) := (lifts f).choose_spec
  refine ⟨t, ?_, ?_, ?_⟩
  · intro i j f
    exact ⟨(ht f).1, (ht f).2.2, (ht f).2.1⟩
  · intro i
    symm
    apply (ht (𝟙 i)).2.2
    simp
  · intro i j k f g
    symm
    apply (ht (f ≫ g)).2.2
    rw [← Category.assoc, (ht f).1, Category.assoc, (ht g).1]
    simp

/-- Clause (2) and the henselian specialization, for the directed system of clause (1).
Source: Stacks Project, More on Algebra, Tag 0A04 and the adjunction in Tag 0A02
(blueprint: lem-weil-pbc-henselization-colimit).

Proof (steps 2--5 of the node):
2. Each stage henselization is henselian by lem-weil-pbc-pair-henselization.
   Apply lem-weil-pbc-filtered-colimit-henselian-pair to obtain the colimit ideal,
   its membership description and henselianness. Transport these to the given colimit
   cocone. The compatible stage structure maps induce eta-infinity by the ring colimit
   property. Ideal.map and the membership descriptions show Ih = I.map eta-infinity.
3. Apply lem-weil-pbc-henselization-universal-property to each map from a stage into
   a henselization of the base colimit. Uniqueness makes these maps a cocone, giving u.
   The colimit pair is henselian, so the same universal property gives the reverse map v.
4. Uniqueness on the base and on each stage proves u and v are inverse.
   The equality Ih = I.map eta-infinity and u composed with eta-infinity = zeta
   show that u carries Ih exactly onto the extended base ideal.
5. If the base colimit pair is henselian, apply the universal property directly to its
   coprojections to obtain beta_i. Uniqueness proves compatibility. Their induced map beta
   is inverse to eta-infinity by the same argument, and carries the colimit ideal onto I.
The colimits here are arbitrary colimit cocones, as in def-weil-pbc-category-colimit. -/
theorem pairHenselization_colimit
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F G : Λ ⥤ CommRingCat.{u}) (η : F ⟶ G)
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (hG : ∀ i : Λ, ∃ c : Cocone (ObjectProperty.ι
        (fun C : Under (F.obj i) ↦
          AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
            Function.Bijective (Ideal.quotientMap ((J i).map C.hom.hom) C.hom.hom
              (Ideal.le_comap_map)))),
        Nonempty (IsColimit c) ∧ ∃ e : c.pt.right ≅ G.obj i,
          c.pt.hom ≫ e.hom = η.app i)
    (c : Cocone F) (hc : IsColimit c) (I : Ideal c.pt)
    (hI : ∀ x : c.pt, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (c.ι.app i).hom a = x ∧ a ∈ J i)
    (d : Cocone G) (hd : IsColimit d) :
    ∃ Ih : Ideal d.pt,
      (∀ x : d.pt, x ∈ Ih ↔ ∃ (i : Λ) (a : G.obj i),
        (d.ι.app i).hom a = x ∧ a ∈ (J i).map (η.app i).hom) ∧
      ∃ ηInf : c.pt ⟶ d.pt,
        (∀ i : Λ, c.ι.app i ≫ ηInf = η.app i ≫ d.ι.app i) ∧
        (∀ (A : CommRingCat.{u}) (ζ : c.pt ⟶ A),
          (∃ ch : Cocone (ObjectProperty.ι
            (fun C : Under c.pt ↦
              AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
                Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
                  (Ideal.le_comap_map)))),
            Nonempty (IsColimit ch) ∧ ∃ e : ch.pt.right ≅ A,
              ch.pt.hom ≫ e.hom = ζ) →
          (∃! u : d.pt ⟶ A, ηInf ≫ u = ζ) ∧
          (∀ u : d.pt ⟶ A, ηInf ≫ u = ζ →
            Function.Bijective u.hom ∧ Ideal.map u.hom Ih = I.map ζ.hom)) ∧
        (HenselianRing c.pt I →
          ∃ β : ∀ i : Λ, G.obj i ⟶ c.pt,
            (∀ i : Λ, η.app i ≫ β i = c.ι.app i ∧
              (∀ b : G.obj i ⟶ c.pt, η.app i ≫ b = c.ι.app i → b = β i) ∧
              Ideal.map (β i).hom ((J i).map (η.app i).hom) ≤ I) ∧
            (∀ {i j : Λ} (f : i ⟶ j), G.map f ≫ β j = β i) ∧
            ∃ b : d.pt ⟶ c.pt,
              (∀ i : Λ, d.ι.app i ≫ b = β i) ∧
              Function.Bijective b.hom ∧ Ideal.map b.hom Ih = I) := by
  classical
  let Jh (i : Λ) : Ideal (G.obj i) := (J i).map (η.app i).hom
  have hJh {i j : Λ} (f : i ⟶ j) : (Jh i).map (G.map f).hom ≤ Jh j := by
    dsimp [Jh]
    rw [Ideal.map_map, ← CommRingCat.hom_comp, ← η.naturality f,
      CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.map_mono (hJ f)
  have hH (i : Λ) : HenselianRing (G.obj i) (Jh i) :=
    henselian_henselization (F.obj i) (G.obj i) (J i) (η.app i) (hG i)
  have : HasColimit G := ⟨⟨d, hd⟩⟩
  obtain ⟨K, hK, _, hHK⟩ := filteredColimit_henselianPair G Jh hJh hH
  have := hHK
  let e := (colimit.isColimit G).coconePointUniqueUpToIso hd
  let Ih := K.map e.hom.hom
  have hHIh : HenselianRing d.pt Ih := henselian_map_equiv K e.commRingCatIsoToRingEquiv
  have hIh (x : d.pt) : x ∈ Ih ↔ ∃ (i : Λ) (a : G.obj i),
      (d.ι.app i).hom a = x ∧ a ∈ Jh i := by
    rw [Ideal.mem_map_iff_of_surjective e.hom.hom e.commRingCatIsoToRingEquiv.surjective]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : ∃ (i : Λ) (a : G.obj i), (colimit.ι G i).hom a = y ∧ a ∈ Jh i := by
        exact (Set.ext_iff.mp hK y).mp hy
      obtain ⟨i, a, rfl, ha⟩ := hy'
      refine ⟨i, a, ?_, ha⟩
      exact congrArg (fun f : G.obj i ⟶ d.pt => f.hom a)
        ((colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hd i).symm
    · rintro ⟨i, a, rfl, ha⟩
      refine ⟨(colimit.ι G i).hom a, ?_, ?_⟩
      · exact (Set.ext_iff.mp hK _).mpr ⟨i, a, rfl, ha⟩
      · exact congrArg (fun f : G.obj i ⟶ d.pt => f.hom a)
          ((colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hd i)
  let cd : Cocone F :=
    { pt := d.pt
      ι := η ≫ d.ι }
  let ηInf := hc.desc cd
  have hη (i : Λ) : c.ι.app i ≫ ηInf = η.app i ≫ d.ι.app i := hc.fac cd i
  have hιJ (i : Λ) : (J i).map (c.ι.app i).hom ≤ I := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (hI _).mpr ⟨i, a, rfl, ha⟩
  have hηI : I.map ηInf.hom ≤ Ih := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    obtain ⟨i, a, rfl, ha⟩ := (hI x).mp hx
    have he := congrArg (fun f : F.obj i ⟶ d.pt => f.hom a) (hη i)
    change ηInf.hom ((c.ι.app i).hom a) =
      (d.ι.app i).hom ((η.app i).hom a) at he
    change ηInf.hom ((c.ι.app i).hom a) ∈ Ih
    rw [he]
    exact (hIh _).mpr ⟨i, (η.app i).hom a, rfl, Ideal.mem_map_of_mem _ ha⟩
  have hIdeq : I.map ηInf.hom = Ih := by
    apply le_antisymm hηI
    intro x hx
    obtain ⟨i, a, rfl, ha⟩ := (hIh x).mp hx
    have hs : (Jh i).map (d.ι.app i).hom ≤ I.map ηInf.hom := by
      dsimp [Jh]
      rw [Ideal.map_map, ← CommRingCat.hom_comp, ← hη i,
        CommRingCat.hom_comp, ← Ideal.map_map]
      exact Ideal.map_mono (hιJ i)
    exact hs (Ideal.mem_map_of_mem _ ha)
  have lift (A : CommRingCat.{u}) (L : Ideal A) [HenselianRing A L]
      (φ : c.pt ⟶ A) (hφ : I.map φ.hom ≤ L) :
      ∃ β : ∀ i : Λ, G.obj i ⟶ A,
        (∀ i : Λ, η.app i ≫ β i = c.ι.app i ≫ φ ∧
          (∀ b : G.obj i ⟶ A, η.app i ≫ b = c.ι.app i ≫ φ → b = β i) ∧
          (Jh i).map (β i).hom ≤ L) ∧
        (∀ {i j : Λ} (f : i ⟶ j), G.map f ≫ β j = β i) ∧
        ∃ b : d.pt ⟶ A, (∀ i : Λ, d.ι.app i ≫ b = β i) ∧
          ηInf ≫ b = φ ∧ (∀ b' : d.pt ⟶ A, ηInf ≫ b' = φ → b' = b) := by
    have lifts (i : Λ) := lift_henselization (F.obj i) (G.obj i) A (J i)
      (η.app i) (hG i) L (c.ι.app i ≫ φ) (by
        rw [CommRingCat.hom_comp, ← Ideal.map_map]
        exact (Ideal.map_mono (hιJ i)).trans hφ)
    let β (i : Λ) := (lifts i).choose
    have hβ (i : Λ) := (lifts i).choose_spec
    have hcomp {i j : Λ} (f : i ⟶ j) : G.map f ≫ β j = β i := by
      apply (hβ i).2.2
      rw [← Category.assoc, ← η.naturality f, Category.assoc, (hβ j).1,
        ← Category.assoc, c.w f]
    let ca : Cocone G :=
      { pt := A
        ι := { app := β, naturality := fun i j f => by simpa using hcomp f } }
    let b := hd.desc ca
    have hb (i : Λ) : d.ι.app i ≫ b = β i := hd.fac ca i
    have hφb : ηInf ≫ b = φ := by
      apply hc.hom_ext
      intro i
      rw [← Category.assoc, hη i, Category.assoc, hb i, (hβ i).1]
    refine ⟨β, fun i => ⟨(hβ i).1, (hβ i).2.2, (hβ i).2.1⟩,
      fun {_ _} f => hcomp f, b, hb, hφb, ?_⟩
    intro b' hb'
    apply hd.hom_ext
    intro i
    rw [hb i]
    apply (hβ i).2.2
    rw [← Category.assoc, ← hη i, Category.assoc, hb']
  refine ⟨Ih, hIh, ηInf, hη, ?_, ?_⟩
  · intro A ζ hA
    have := henselian_henselization c.pt A I ζ hA
    obtain ⟨_, _, _, u, _, hu, huniq⟩ := lift A (I.map ζ.hom) ζ le_rfl
    refine ⟨⟨u, hu, huniq⟩, ?_⟩
    intro u' hu'
    have := hHIh
    obtain ⟨v, hv, _, _⟩ := lift_henselization c.pt A d.pt I ζ hA Ih ηInf hηI
    have huv : u' ≫ v = 𝟙 d.pt := by
      obtain ⟨_, _, _, _, _, _, huni⟩ := lift d.pt Ih ηInf hηI
      exact (huni (u' ≫ v) (by rw [← Category.assoc, hu', hv])).trans
        (huni (𝟙 d.pt) (Category.comp_id ηInf)).symm
    have hvu : v ≫ u' = 𝟙 A := by
      obtain ⟨_, _, _, huni⟩ := lift_henselization c.pt A A I ζ hA
        (I.map ζ.hom) ζ le_rfl
      exact (huni (v ≫ u') (by rw [← Category.assoc, hv, hu'])).trans
        (huni (𝟙 A) (by simp)).symm
    have bij : Function.Bijective u'.hom := by
      constructor
      · intro x y hxy
        have he (a : d.pt) : v.hom (u'.hom a) = a :=
          congrArg (fun f : d.pt ⟶ d.pt => f.hom a) huv
        rw [← he x, ← he y, hxy]
      · intro a
        exact ⟨v.hom a, congrArg (fun f : A ⟶ A => f.hom a) hvu⟩
    refine ⟨bij, ?_⟩
    rw [← hIdeq, Ideal.map_map, ← CommRingCat.hom_comp, hu']
  · intro hbase
    have := hbase
    obtain ⟨β, hβ, hcomp, b, hb, hηb, _⟩ := lift c.pt I (𝟙 c.pt) (by simp)
    have := hHIh
    obtain ⟨_, _, _, _, _, _, huni⟩ := lift d.pt Ih ηInf hηI
    have hbη : b ≫ ηInf = 𝟙 d.pt := by
      exact (huni (b ≫ ηInf) (by rw [← Category.assoc, hηb]; simp)).trans
        (huni (𝟙 d.pt) (Category.comp_id ηInf)).symm
    refine ⟨β, ?_, hcomp, b, hb, ?_, ?_⟩
    · intro i
      simpa using hβ i
    · constructor
      · intro x y hxy
        have he (a : d.pt) : ηInf.hom (b.hom a) = a :=
          congrArg (fun f : d.pt ⟶ d.pt => f.hom a) hbη
        rw [← he x, ← he y, hxy]
      · intro a
        exact ⟨ηInf.hom a, congrArg (fun f : c.pt ⟶ c.pt => f.hom a) hηb⟩
    · rw [← hIdeq, Ideal.map_map, ← CommRingCat.hom_comp, hηb]
      simp


end RingTheory
