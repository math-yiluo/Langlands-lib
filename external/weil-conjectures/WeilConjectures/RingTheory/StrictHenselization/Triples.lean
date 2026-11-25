/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# Étale algebras with a point and a residue embedding

Let `R` be a commutative ring, `p` a prime of `R` and `K` a field over `R`. An *étale triple*
`(S, q, φ)` consists of an étale `R`-algebra `S`, a prime `q` of `S` lying over `p` and an
`R`-algebra map `φ : κ(q) → K` (equivalently a `κ(p)`-algebra map, as `κ(p)` is a localization
of a quotient of `R`). A morphism `(S, q, φ) ⟶ (S', q', φ')` is an `R`-algebra map
`β : S → S'` with `β⁻¹(q') = q` and `φ' ∘ κ(β) = φ`.

We show that the étale triples form a filtered, finally small category, so that the colimit
`C = colim S` over the triples exists; when `K` is a separable closure of `κ(p)`, this colimit is
the strict henselization of `R_p` (see
`WeilConjectures.RingTheory.StrictHenselization.TriplesHenselian`).

A triple `t = (S, q, φ)` is the same as an étale `R`-algebra `S` with an `R`-algebra map
`t.toAlgHom : S → κ(q) → K` (`EtaleTriple.ofAlgHom`), and the morphisms of triples are the
`R`-algebra maps commuting with these maps (`EtaleTriple.Hom.toAlgHom_comp`,
`EtaleTriple.homMk`).

## Main definitions

- `EtaleTriple R p K`: the category of étale triples.
- `EtaleTriple.diagram R p K`: the functor `(S, q, φ) ↦ S` to `R`-algebras.
- `EtaleTriple.colim R p K`: its colimit.
- `EtaleTriple.eval R p K`: the `R`-algebra map `colim S → K` induced by the maps `S → K`.

## References

- Stacks Project, Lemma 10.155.5, <https://stacks.math.columbia.edu/tag/04GW>
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

variable (R : Type u) [CommRing R] (p : Ideal R) (K : Type u) [Field K] [Algebra R K]

/-- An *étale triple* `(S, q, φ)` over `(R, p, K)`: an étale `R`-algebra `S`, a prime `q` of `S`
lying over `p` and an `R`-algebra map `φ : κ(q) → K` from the residue field of `q`.

(blueprint: `lem-weil-pbc-strict-henselization-triples`,
`proposition-proper-base-change-projective-line--1`) -/
structure EtaleTriple where
  /-- the étale `R`-algebra -/
  S : Type u
  [commRing : CommRing S]
  [algebra : Algebra R S]
  [etale : Algebra.Etale R S]
  /-- the prime of `S` -/
  q : Ideal S
  [isPrime : q.IsPrime]
  comap_eq : q.comap (algebraMap R S) = p
  /-- the residue embedding -/
  φ : q.ResidueField →ₐ[R] K

namespace EtaleTriple

attribute [instance] commRing algebra etale isPrime

variable {R p K}

/-- The `R`-algebra map `S → κ(q) → K` of an étale triple `(S, q, φ)`. -/
noncomputable def toAlgHom (t : EtaleTriple R p K) : t.S →ₐ[R] K :=
  t.φ.comp (IsScalarTower.toAlgHom R t.S t.q.ResidueField)

lemma toAlgHom_apply (t : EtaleTriple R p K) (s : t.S) :
    t.toAlgHom s = t.φ (algebraMap t.S t.q.ResidueField s) :=
  rfl

/-- The kernel of `S → K` is the prime `q` of the triple. -/
lemma ker_toAlgHom (t : EtaleTriple R p K) : RingHom.ker t.toAlgHom = t.q := by
  have : Function.Injective t.φ := t.φ.toRingHom.injective
  ext s
  rw [RingHom.mem_ker, toAlgHom_apply, map_eq_zero_iff _ this,
    Ideal.algebraMap_residueField_eq_zero]

/-- A morphism of étale triples `(S, q, φ) ⟶ (S', q', φ')`: an `R`-algebra map `β : S → S'`
with `β⁻¹(q') = q` and `φ' ∘ κ(β) = φ`. -/
@[ext]
structure Hom (t t' : EtaleTriple R p K) where
  /-- the underlying algebra map -/
  β : t.S →ₐ[R] t'.S
  comap_eq : t'.q.comap β.toRingHom = t.q
  φ_comp : t'.φ.comp (Ideal.ResidueField.mapₐ t.q t'.q β comap_eq.symm) = t.φ

/-- A morphism of étale triples commutes with the maps to `K`. -/
lemma Hom.toAlgHom_comp {t t' : EtaleTriple R p K} (f : Hom t t') :
    t'.toAlgHom.comp f.β = t.toAlgHom := by
  ext s
  rw [AlgHom.comp_apply, toAlgHom_apply, toAlgHom_apply, ← f.φ_comp, AlgHom.comp_apply,
    Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap]
  rfl

/-- An `R`-algebra map between the algebras of two étale triples which commutes with the maps
to `K` is a morphism of triples. -/
noncomputable def homMk {t t' : EtaleTriple R p K} (β : t.S →ₐ[R] t'.S)
    (h : t'.toAlgHom.comp β = t.toAlgHom) : Hom t t' where
  β := β
  comap_eq := by
    rw [← ker_toAlgHom, ← ker_toAlgHom, ← h]
    rfl
  φ_comp := by
    ext s
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.ResidueField.mapₐ_apply,
      Ideal.ResidueField.map_algebraMap]
    exact congr($h s)

@[simp]
lemma homMk_β {t t' : EtaleTriple R p K} (β : t.S →ₐ[R] t'.S)
    (h : t'.toAlgHom.comp β = t.toAlgHom) : (homMk β h).β = β :=
  rfl

noncomputable instance : Category (EtaleTriple R p K) where
  Hom := Hom
  id t := homMk (AlgHom.id R t.S) (AlgHom.comp_id _)
  comp f g := homMk (g.β.comp f.β) (by rw [← AlgHom.comp_assoc, g.toAlgHom_comp, f.toAlgHom_comp])

@[ext]
lemma hom_ext {t t' : EtaleTriple R p K} {f g : t ⟶ t'} (h : f.β = g.β) : f = g :=
  Hom.ext h

@[simp]
lemma id_β (t : EtaleTriple R p K) : Hom.β (𝟙 t) = AlgHom.id R t.S :=
  rfl

@[simp]
lemma comp_β {t t' t'' : EtaleTriple R p K} (f : t ⟶ t') (g : t' ⟶ t'') :
    Hom.β (f ≫ g) = g.β.comp f.β :=
  rfl

/-- The étale triple attached to an étale `R`-algebra `S` with an `R`-algebra map `χ : S → K`,
when the kernel of `R → K` is `p`: its prime is the kernel of `χ`, and its residue embedding is
the map induced by `χ`. -/
noncomputable def ofAlgHom (hK : RingHom.ker (algebraMap R K) = p) (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (χ : S →ₐ[R] K) : EtaleTriple R p K where
  S := S
  q := RingHom.ker χ
  isPrime := RingHom.ker_isPrime _
  comap_eq := by
    rw [← hK]
    ext r
    simp
  φ :=
    letI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
    Ideal.ResidueField.liftₐ _ χ le_rfl fun s hs ↦ by
      simpa [IsUnit.submonoid, isUnit_iff_ne_zero] using hs

@[simp]
lemma ofAlgHom_S (hK : RingHom.ker (algebraMap R K) = p) (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (χ : S →ₐ[R] K) : (ofAlgHom hK S χ).S = S :=
  rfl

@[simp]
lemma toAlgHom_ofAlgHom (hK : RingHom.ker (algebraMap R K) = p) (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (χ : S →ₐ[R] K) : (ofAlgHom hK S χ).toAlgHom = χ := by
  have : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
  ext s
  rw [toAlgHom_apply]
  exact Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ _

end EtaleTriple

namespace EtaleTriple

variable {R p K} [p.IsPrime] [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K]

variable (R p K) in
/-- The kernel of `R → κ(p) → K` is `p`. -/
lemma ker_algebraMap : RingHom.ker (algebraMap R K) = p := by
  rw [IsScalarTower.algebraMap_eq R p.ResidueField K, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap p.ResidueField K).injective,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

variable (R p K) in
/-- The étale triple `(R, p, κ(p) → K)`. -/
noncomputable def base : EtaleTriple R p K :=
  ofAlgHom (ker_algebraMap R p K) R (Algebra.ofId R K)

/-- Any two étale triples map to a common one, the tensor product of their algebras. -/
lemma exists_hom_hom (t t' : EtaleTriple R p K) :
    ∃ (t'' : EtaleTriple R p K) (_ : t ⟶ t'') (_ : t' ⟶ t''), True := by
  have : Algebra.Etale R (t.S ⊗[R] t'.S) := Algebra.Etale.comp R t.S _
  let χ : t.S ⊗[R] t'.S →ₐ[R] K :=
    Algebra.TensorProduct.lift t.toAlgHom t'.toAlgHom fun _ _ ↦ Commute.all _ _
  let t'' := ofAlgHom (ker_algebraMap R p K) _ χ
  refine ⟨t'', homMk (t' := t'') Algebra.TensorProduct.includeLeft ?_,
    homMk (t' := t'') Algebra.TensorProduct.includeRight ?_, trivial⟩
  · rw [toAlgHom_ofAlgHom]
    ext s
    exact (Algebra.TensorProduct.lift_tmul _ _ (fun _ _ ↦ Commute.all _ _) s 1).trans (by simp)
  · rw [toAlgHom_ofAlgHom]
    ext s
    exact (Algebra.TensorProduct.lift_tmul _ _ (fun _ _ ↦ Commute.all _ _) 1 s).trans (by simp)

/-- Two parallel morphisms of étale triples are coequalized by a morphism of étale triples.

If `β₁, β₂ : S → S'`, the kernel of the multiplication `S ⊗[R] S → S` is generated by an
idempotent `e` (`S` is unramified over `R`); the map `S' → S'[1/u]` for `u` the image of `1 - e`
under `β₁ ⊗ β₂` coequalizes `β₁` and `β₂`, and `S'[1/u]` is an étale triple since `u` maps to
`1` in `K`. (This is the étale neighbourhood `S' ⊗_{S ⊗[R] S} S` of the blueprint.) -/
lemma exists_hom_comp_eq_comp {t t' : EtaleTriple R p K} (f g : t ⟶ t') :
    ∃ (t'' : EtaleTriple R p K) (h : t' ⟶ t''), f ≫ h = g ≫ h := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧
      KaehlerDifferential.ideal R t.S = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R t.S)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[t.S⁄R]
  let β : t.S ⊗[R] t.S →ₐ[R] t'.S :=
    Algebra.TensorProduct.lift f.β g.β fun _ _ ↦ Commute.all _ _
  have hβ : t'.toAlgHom.comp β = t.toAlgHom.comp (Algebra.TensorProduct.lmul' R) := by
    ext a
    · simpa [β] using congr($(f.toAlgHom_comp) a)
    · simpa [β] using congr($(g.toAlgHom_comp) a)
  have he₀ : Algebra.TensorProduct.lmul' R e = 0 := by
    have : e ∈ KaehlerDifferential.ideal R t.S := hsp ▸ Ideal.mem_span_singleton_self e
    exact this
  let u := β (1 - e)
  have hu : IsUnit (t'.toAlgHom u) := by
    have : t'.toAlgHom u = 1 := by
      change (t'.toAlgHom.comp β) (1 - e) = 1
      rw [hβ, AlgHom.comp_apply, map_sub, he₀, map_one, sub_zero, map_one]
    simp [this]
  let S'' := Localization.Away u
  let χ : S'' →ₐ[R] K := IsLocalization.liftAlgHom (M := Submonoid.powers u)
    (f := t'.toAlgHom) (by rintro ⟨_, n, rfl⟩; simpa using hu.pow n)
  let t'' := ofAlgHom (ker_algebraMap R p K) S'' χ
  have hχ : t''.toAlgHom.comp (IsScalarTower.toAlgHom R t'.S S'') = t'.toAlgHom := by
    rw [toAlgHom_ofAlgHom]
    ext s
    exact IsLocalization.lift_eq (S := Localization.Away u) _ s
  refine ⟨t'', homMk (t' := t'') _ hχ, hom_ext ?_⟩
  have hβe : algebraMap t'.S S'' (β e) = 0 := by
    have h1 : IsUnit (algebraMap t'.S S'' u) := IsLocalization.Away.algebraMap_isUnit u
    have h2 : algebraMap t'.S S'' (β e) * algebraMap t'.S S'' u = 0 := by
      rw [← map_mul, ← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero, map_zero]
    exact (h1.mul_left_eq_zero).mp h2
  ext s
  have hs : s ⊗ₜ[R] (1 : t.S) - 1 ⊗ₜ s ∈ Ideal.span {e} := by
    rw [← hsp]
    change Algebra.TensorProduct.lmul' R (s ⊗ₜ[R] (1 : t.S) - 1 ⊗ₜ s) = 0
    simp
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hs
  have : f.β s - g.β s = β x * β e := by
    rw [← map_mul, hx, map_sub]
    simp [β]
  change algebraMap t'.S S'' (f.β s) = algebraMap t'.S S'' (g.β s)
  rw [← sub_eq_zero, ← map_sub, this, map_mul, hβe, mul_zero]

instance : IsFiltered (EtaleTriple R p K) where
  cocone_objs t t' := exists_hom_hom t t'
  cocone_maps _ _ f g := exists_hom_comp_eq_comp f g
  nonempty := ⟨base R p K⟩

/-- Every étale triple is isomorphic, through a morphism of triples, to one whose algebra is a
quotient of a polynomial ring in finitely many variables over `R`. -/
lemma exists_hom_quotient (t : EtaleTriple R p K) :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R))
      (_ : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ I))
      (χ : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] K),
      Nonempty (t ⟶ ofAlgHom (ker_algebraMap R p K) _ χ) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType R t.S)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have := Algebra.Etale.of_equiv e.symm
  refine ⟨n, _, this, t.toAlgHom.comp e.toAlgHom, ⟨homMk e.symm.toAlgHom ?_⟩⟩
  rw [toAlgHom_ofAlgHom]
  ext s
  simp

instance : FinallySmall.{u} (EtaleTriple R p K) := by
  let ι := Σ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)),
    PLift (Algebra.Etale R (MvPolynomial (Fin n) R ⧸ I)) × ((MvPolynomial (Fin n) R ⧸ I) →ₐ[R] K)
  let F : ι → EtaleTriple R p K := fun i ↦
    have := i.2.2.1.down
    ofAlgHom (ker_algebraMap R p K) _ i.2.2.2
  refine finallySmall_of_small_weakly_terminal_set (Set.range F) fun t ↦ ?_
  obtain ⟨n, I, h, χ, ⟨f⟩⟩ := exists_hom_quotient t
  exact ⟨_, ⟨⟨n, I, ⟨h⟩, χ⟩, rfl⟩, ⟨f⟩⟩

variable (R p K)

/-- The diagram `(S, q, φ) ↦ S` of `R`-algebras over the étale triples.
(blueprint: `proposition-proper-base-change-projective-line--1`) -/
noncomputable def diagram : EtaleTriple R p K ⥤ CommAlgCat.{u} R where
  obj t := CommAlgCat.of R t.S
  map f := CommAlgCat.ofHom f.β

instance : HasColimitsOfShape (EtaleTriple R p K) (CommAlgCat.{u} R) :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The colimit `C = colim S` of the algebras of the étale triples.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
noncomputable def colim : CommAlgCat.{u} R :=
  colimit (diagram R p K)

/-- The coprojection `S → C` of an étale triple. -/
noncomputable def ι (t : EtaleTriple R p K) : t.S →ₐ[R] colim R p K :=
  (colimit.ι (diagram R p K) t).hom

@[simp]
lemma ι_comp_β {t t' : EtaleTriple R p K} (f : t ⟶ t') : (ι R p K t').comp f.β = ι R p K t := by
  have := colimit.w (diagram R p K) f
  exact congr(($this).hom)

/-- The cocone `(S ⟶ K)` given by the maps of the étale triples. -/
noncomputable def evalCocone : Cocone (diagram R p K) where
  pt := CommAlgCat.of R K
  ι := { app t := CommAlgCat.ofHom t.toAlgHom
         naturality _ _ f := by
           ext1
           exact (Hom.toAlgHom_comp f).trans (AlgHom.comp_id _).symm }

/-- The map `ψ : C → K` induced by the maps `S → κ(q) → K` of the étale triples.

(blueprint: `lem-weil-pbc-strict-henselization-triples`) -/
noncomputable def eval : colim R p K →ₐ[R] K :=
  (colimit.desc (diagram R p K) (evalCocone R p K)).hom

@[simp]
lemma eval_ι (t : EtaleTriple R p K) (s : t.S) : eval R p K (ι R p K t s) = t.toAlgHom s := by
  have := colimit.ι_desc (evalCocone R p K) t
  exact congr(($this).hom s)

/-- Every element of the colimit `C` comes from some étale triple. -/
lemma exists_ι_eq (x : colim R p K) : ∃ (t : EtaleTriple R p K) (s : t.S), ι R p K t s = x := by
  have : PreservesColimitsOfShape (EtaleTriple R p K) (forget (CommAlgCat.{u} R)) :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered.{u} _ _
  exact Concrete.colimit_exists_rep (diagram R p K) x

end EtaleTriple
