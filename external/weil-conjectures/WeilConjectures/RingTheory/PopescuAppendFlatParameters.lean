/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.PopescuInitialFlatCoordinates
import WeilConjectures.RingTheory.FlatRegularFibreParameterSelection
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Appending parameters to a residue differential basis

Source: Stacks Project, proof of Tag 07FH, construction of property (1), and
More on Algebra, Tag 07E6.
-/

@[expose] public section

set_option autoImplicit false
universe u v w
namespace Algebra

/-- Appending selected maximal-ideal generators to fixed differential coordinates gives
flat polynomial coordinates. No admissible subalgebra or enlargement is constructed here.
Source: Stacks Project, proof of Tag 07FH, from the choice of the differential basis
through property (1); More on Algebra, Tag 07E6.
(blueprint: lem-weil-pbc-popescu-append-flat-parameters).

Proof: Localize the geometrically regular algebra at `q`; geometric regularity persists,
because purely inseparable scalar extension commutes with localization and localization
preserves regular rings. Identify `F` with its image under `ι`, a finitely generated
intermediate field of the residue field (essential finite type for field extensions is
finite generation). Apply 07E6 to the polynomial map on `xs` and the given differential
basis. This gives a flat map from the first polynomial localization and a regular local
closed fibre `S`. The images of `ys` generate its maximal ideal. Extract a basis from their
images in the cotangent space, and retain the corresponding indices `s`. Nakayama makes
these selected elements generators of the maximal ideal of `S`; their number is its
embedding dimension, hence its dimension. They are therefore a regular system of parameters
and a regular sequence by 00NQ. Append precisely these `ys (s i)` to `xs`, using `Fin.addCases`.
The contracted prime contains the added variables. Its extended ideal is contained in
`q` and contains the first-coordinate ideal and the selected parameters, whose sum is `q`
after localization, proving the ideal equality. The fibre of the extended polynomial
localization over the first one is the polynomial ring over the first residue field
localized at the origin: its prime contains all new variables, which already generate a
maximal ideal. By 00OP it is regular local, with the new variables as parameters. Their
images in `S` are a regular sequence, so 07DY gives flatness of the closed-fibre map.
Finally 00MP, applied to the first polynomial localization, the extended one, and
`Localization.AtPrime q` as a module over itself, lifts this fibre flatness and the initial
flatness to flatness of the extended map. Its restriction to the polynomial ring is the
explicit `aeval` map by the localization universal property.

If `t = 0`, 07E6 still applies to the empty basis. If the closed fibre is a field, choose
`e = 0`. If `r = 0`, the localized maximal ideal is zero, so this latter case applies.
No injectivity of the selected indexing function is required by the conclusion. -/
theorem exists_popescu_append_flat_parameters
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (F : Type w) [Field F] [Algebra k F] [EssFiniteType k F]
    (ι : F →ₐ[k] q.ResidueField)
    (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ) (a : Fin t → F)
    (ha : ∀ j, ι (a j) = IsLocalRing.residue (Localization.AtPrime q)
      (algebraMap Λ (Localization.AtPrime q) (xs j)))
    (b : Module.Basis (Fin t) F (KaehlerDifferential k F))
    (hb : ∀ j, b j = KaehlerDifferential.D k F (a j))
    (hyq : ∀ i, ys i ∈ q)
    (hys : Ideal.span (Set.range (fun i ↦ algebraMap Λ (Localization.AtPrime q) (ys i))) =
      q.map (algebraMap Λ (Localization.AtPrime q))) :
    ∃ (e : ℕ) (s : Fin e → Fin r),
      let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
        MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
      ∃ ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q,
        ψ.comp (algebraMap (MvPolynomial (Fin (t + e)) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) =
          (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap φ.toRingHom).map
            ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
        ψ.Flat := by
  obtain ⟨hflat₀, hfibre₀⟩ :=
    popescu_initial_flat_coordinates k Λ p hp hreg q F ι t xs a ha b hb
  obtain ⟨e, s, hflat, hgen⟩ :=
    exists_flat_regular_fibre_parameter_selection k Λ q t r xs ys hyq hys hflat₀ hfibre₀
  let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
    MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
  let g := (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom
  let J := (q.comap φ.toRingHom).map g
  refine ⟨e, s, Localization.localRingHom (q.comap φ.toRingHom) q φ.toRingHom rfl,
    ?_, ?_, hflat⟩
  · apply RingHom.ext
    intro f
    exact Localization.localRingHom_to_map (q.comap φ.toRingHom) q φ.toRingHom rfl f
  · change q.map (algebraMap Λ (Localization.AtPrime q)) = J
    apply le_antisymm
    · rw [hgen]
      apply sup_le
      · apply Ideal.map_le_iff_le_comap.mpr
        intro f hf
        have heval : φ (MvPolynomial.rename (Fin.castAdd e) f) =
            MvPolynomial.aeval xs f := by
          simp [φ, MvPolynomial.aeval_rename, Function.comp_def]
        have hmem : MvPolynomial.rename (Fin.castAdd e) f ∈ q.comap φ.toRingHom := by
          change φ (MvPolynomial.rename (Fin.castAdd e) f) ∈ q
          rw [heval]
          exact hf
        have h := Ideal.mem_map_of_mem g hmem
        change (algebraMap Λ (Localization.AtPrime q))
          (φ (MvPolynomial.rename (Fin.castAdd e) f)) ∈ J at h
        rw [heval] at h
        exact h
      · apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        have heval : φ (MvPolynomial.X (Fin.natAdd t i)) = ys (s i) := by
          simp [φ]
        have hmem : MvPolynomial.X (Fin.natAdd t i) ∈ q.comap φ.toRingHom := by
          change φ (MvPolynomial.X (Fin.natAdd t i)) ∈ q
          rw [heval]
          exact hyq (s i)
        have h := Ideal.mem_map_of_mem g hmem
        change (algebraMap Λ (Localization.AtPrime q))
          (φ (MvPolynomial.X (Fin.natAdd t i))) ∈ J at h
        rw [heval] at h
        exact h
    · change (q.comap φ.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ≤ _
      rw [← Ideal.map_map]
      exact Ideal.map_mono Ideal.map_comap_le

end Algebra
