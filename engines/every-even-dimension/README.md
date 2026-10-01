# Engines of «The Watermark in Every Even Dimension»

Scripts and logs of the seven engines of §8 of the note (`papers/THE_WATERMARK_IN_EVERY_EVEN_DIMENSION.pdf`). Python 3 with numpy and sympy; engine 3 needs Macaulay2.

Every run was made inside the guard `vigia.sh` (1.2 GB, 10 minutes): `zsh vigia.sh LOG 'command'`. The last line of each log says how the run ended. Logs that end with `VIGIA-MATADO-…` are runs stopped by the guard; they are kept and not used.

| engine | folder | script |
|---|---|---|
| 1. Lattice of the linear spaces | `lattice-points-ring-walks/` | `gram_smith.py n p [M]` |
| 2. Hilbert functions of the points | `lattice-points-ring-walks/` | `hilbert2.py n p full\|short` |
| 3. The ring in (C), Macaulay2 | `lattice-points-ring-walks/` | `ta_even.py k p [char]` |
| 4. Walk statistic, and the interpolation | `lattice-points-ring-walks/` | `E_estadistica2.py`, `ajuste.py` |
| 5. Orders and delta invariants | `orders-group-pham/` | `delta_ordenes.py n p [M]` |
| 6. The discriminant group as a ring | `orders-group-pham/` | `grupo_discriminante.py`, `grupo_general.py`, `grupo_lector_en_frio.py` |
| 7. The lattices from Looijenga's form | `orders-group-pham/` | `pham_gram.py n p` |

Summary logs: `orders-group-pham/recuento_caja_par_car_p.log` (condition (C) in 22 cells), `orders-group-pham/conos_tangentes_A_T.log` (Conjecture S in 13 cells), `lattice-points-ring-walks/ajuste.log` (the polynomials), `lattice-points-ring-walks/verif_nota.log`, `recheck_tabla.log`.

The file names are in Spanish because they are the working files of the project.

The cold reader's own engines and logs are in `cold-reading/every-even-dimension/cold/`.
