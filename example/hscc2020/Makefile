all: mean.summary.standalone.pdf mean.M1.plot.standalone.pdf

%.summary.standalone.pdf: %.summary.standalone.tex %.summary.tabular.tex
	cd $(dir $<) && pdflatex $(notdir $<)

%.plot.standalone.pdf: %.plot.standalone.tex %.plot.tikz.tex
	cd $(dir $<) && pdflatex $(notdir $<)

%.plot.standalone.tex: summary.standalone.tex.m4
	m4 -DINPUT=$(basename $(basename $(notdir $@))).tikz $< > $@

%.summary.standalone.tex: summary.standalone.tex.m4
	m4 -DINPUT=$(basename $(basename $(notdir $@))).tabular $< > $@

mean.M1.plot.tikz.tex: mean.M1.summary.tsv mean.M1.plot.tikz.plt
	gnuplot mean.M1.plot.tikz.plt

%.summary.tabular.tex: %.summary.header %.summary.tabular.body.tex
	cat $^ > $@

%.summary.tabular.body.tex: %.summary.tsv ./utils/tsv2tabular.awk
	cat $< | ./utils/tsv2tabular.awk > $@

%.M1.summary.tsv: %.summary.tsv
	cat $< | grep 'stlFml_{6' | awk '/tiny/{$$1="2"}/small/{$$1="4"}/medium/{$$1="8"}/large/{$$1="12"}/huge/{$$1="18"}/gigantic/{$$1="36"} 1;' | tr '/ ' '\t\t' > $@

%.summary.tsv: %.result.tsv
	cat $< | awk '!l[$$1]{l[$$1] = c+1;c += 1;} {print l[$$1]$$0}' | datamash crosstab 1,2 collapse 3 | sort -n | sed 's/\\\\/\\/g;s/^[0-9]*//;' | awk 'NR>1' > $@

mean-std.result.tsv: result.with.number.tsv
	awk '{OFS="\t";print $$1,$$2,$$3"/"$$7" "$$4"/"$$8}' $< > $@ 

mean.result.tsv: result.with.number.tsv
	awk '{OFS="\t";print $$1,$$2,$$3"/"$$7}' $< > $@

all.result.tsv: result.with.number.tsv
	awk '{OFS="\t";print $$1,$$2,$$3"/"$$7" "$$4"/"$$8" "$$5"/"$$9" "$$6"/"$$10}' $< > $@

result.with.number.tsv: result.tsv
	awk '$$2 == "random"{$$2="1random"}$$2 == "hc"{$$2="2hc"}$$2 == "ga"{$$2="3ga"}$$2 == "breach"{$$2="4breach"}1;' $< > $@

mean.states.summary.tsv: constructed_states.tsv
	cat $< | awk 'BEGIN{OFS="\t"}$$2 == "random"{$$2="1random"}$$2 == "hc"{$$2="2hc"}$$2 == "ga"{$$2="3ga"}1;' | cut -f 1-3 | datamash crosstab 1,2 collapse 3 | sed '1d;s/\\\\/\\/g' > $@

all.states.summary.tsv: constructed_states.tsv
	cat $< | awk '$$2 == "random"{$$2="1random"}$$2 == "hc"{$$2="2hc"}$$2 == "ga"{$$2="3ga"}1;' | sort | awk '{OFS="\t";print $$1,$$2,$$3" "$$4" "$$5" "$$6}' | sort | datamash crosstab 1,2 collapse 3 | sed 's/\\\\/\\/g' | awk 'NR>1'> $@

result.tsv: result_name.list.txt ./utils/list2result.awk ./utils/makeRawNumTime.sh
	./utils/list2result.awk < $< | tr ' ' '\t' | sed 's/[rR][aA][nN][dD][oO][mM]/random/g;s/[gG][aA]/ga/g;s/[hH][cC]/hc/g;' > $@

%.list.txt: %.json
	./utils/parsrj.sh < $< | awk -F . '{print $$2,$$3}' > $@

%.json: %.yaml
	ruby -ryaml -rjson -e 'puts JSON.pretty_generate(YAML.load(STDIN.read))' < $< > $@

constructed_states.tsv: result_name.list.txt ./utils/list2states.awk ./utils/makeStateSize.sh
	grep -v breach $< | ./utils/list2states.awk  | tr ' ' '\t' > $@

clean:
	$(RM) result.tsv result_name.{list.txt,json} {all,mean-std,all.states,mean.states}.summary.{standalone.{pdf,tex,aux,log},tabular.tex,tabular.body.tex,tsv} constructed_states.tsv mean.M1.plot.tikz.tex mean.M1 mean.M1.plot.standalone.{aux,log,pdf}

.PHONY: clean all
