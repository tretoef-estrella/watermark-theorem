cd /Users/rafa/Desktop/ARBOLYAML/ARISTOTLE_LEAN/WATERMARK/proyecto
LOG=../clean_rebuild_2026-09-30.log
echo "clean rebuild start $(date '+%H:%M:%S')" > $LOG
for mod in Main Watermark.Defs Watermark.W1 Watermark.W2 Watermark.W3 Watermark.W4 Watermark.W5 Watermark.W6 Watermark.W7; do
  s=$(date +%s)
  TOPE_KB=3145728 TOPE_S=900 zsh /Users/rafa/Desktop/ARBOLYAML/corpus4/herramientas_grepy/vigia.sh ../cr_$mod.log "lake build RequestProject.$mod"
  echo "RequestProject.$mod exit_line: $(tail -1 ../cr_$mod.log) wall=$(( $(date +%s) - s ))s" >> $LOG
done
TOPE_KB=3145728 TOPE_S=900 zsh /Users/rafa/Desktop/ARBOLYAML/corpus4/herramientas_grepy/vigia.sh ../cr_all.log "lake build"
echo "plain lake build: $(grep -E 'Build completed|error' ../cr_all.log | tail -1) $(tail -1 ../cr_all.log)" >> $LOG
echo "clean rebuild end $(date '+%H:%M:%S')" >> $LOG
