#!/usr/bin/python3

import pandas, seaborn, matplotlib.pyplot
from latest_benchmark_results import data as c_data
from latest_benchmark_ocaml_results import data as ocaml_data

ALIASES = {
    'benchmark': [
        ('fnv1a64', 'fnv1a'),
        ('utf8_decode', 'utf8'),
        ('murmur3', 'm3s'),
        ('upstr', 'upstr'),
        ('ip_checksum', 'ip'),
        ('revcomp', 'fasta'),
        ('crc32', 'crc32'),
    ],
    'compiler': [
        ("gcc-9.4.0", "GCC 9.4"),
        ("gcc-10.3.0", "GCC 10.3"),
        ("gcc-11.1.0", "GCC 11.1"),
        ("clang-10.0.0", "Clang 10.0"),
        ("clang-11.0.0", "Clang 11.0"),
        ("clang-12.0.0", "Clang 12.0"),
        ("clang-13.0.1", "Clang 13.0"),
        ("ocamlopt-4.09.0", "ocamlopt 4.09")
    ],
    'language': [
        ("rupicola", "Rupicola"),
        ("c",        "C"),
        ("ocaml-spec-naive",  "Coq/OCaml (sound)"),
        ("ocaml-impl-naive",  "Coq/OCaml Impl (sound)"),
        ("ocaml-spec-extr",   "Coq/OCaml"),
        ("ocaml-impl-extr",   "Coq/OCaml Impl"),
    ]
}

COLORS = {
    ('GCC 9.4',       'C'):                      '#5c3566',
    ('GCC 10.3',      'C'):                      '#75507b',
    ('GCC 11.1',      'C'):                      '#ad7fa8',
    ('GCC 9.4',       'Rupicola'):               '#8f5902',
    ('GCC 10.3',      'Rupicola'):               '#c17d11',
    ('GCC 11.1',      'Rupicola'):               '#e9b96e',

    ('Clang 11.0',    'C'):                      '#204a87',
    ('Clang 12.0',    'C'):                      '#3465a4',
    ('Clang 13.0',    'C'):                      '#729fcf',
    ('Clang 11.0',    'Rupicola'):               '#ce5c00',
    ('Clang 12.0',    'Rupicola'):               '#f57900',
    ('Clang 13.0',    'Rupicola'):               '#fcaf3e',

    ('ocamlopt 4.09', 'Coq/OCaml Impl'):         '#a40000',
    ('ocamlopt 4.09', 'Coq/OCaml'):              '#cc0000',
    ('ocamlopt 4.09', 'Coq/OCaml Impl (sound)'): '#ef2929',
    ('ocamlopt 4.09', 'Coq/OCaml (sound)'):      '#ef2929',
}

def prepare(data, selected_benchmarks):
    df = pandas.DataFrame(data).explode(3)
    df[3] = df[3].apply(lambda x: x/1024/1024)
    df.columns=['benchmark', 'language', 'compiler', 'cycles/byte']

    for col, repls in ALIASES.items():
        df[col].replace(*zip(*repls), inplace=True)
    if selected_benchmarks is not None:
        df = df.loc[df['benchmark'].isin(selected_benchmarks)]

    df['bench']  = df['language'] + "/" + df['benchmark']
    df['config'] = df['language'] + " " + df['compiler']

    return df

def add_plot(data, configs, xlabel, selected_benchmarks=None, ax=None, logmin=False):
    df = prepare(data, selected_benchmarks)
    seaborn.set_palette(seaborn.color_palette([COLORS[c] for c in configs]))
    hue_order = [lang + " " + comp for (comp, lang) in configs]

    if selected_benchmarks is None:
        selected_benchmarks = [k for _, k in ALIASES['benchmark']]

    ax = seaborn.barplot(
        ax=ax,
        data=df,
        x='cycles/byte', y='benchmark',
        hue='config', hue_order=hue_order,
        order=selected_benchmarks,
        linewidth=0, saturation=0.75,
        ci=0.95, n_boot=1000, seed=0,
    )

    ax.set_xlabel(xlabel)
    ax.set_ylabel("")
    ax.yaxis.set_tick_params(length=0)

    if logmin:
        ax.set(xscale="log")
        ax.set(xlim=(logmin, None))

    return ax

def c_benchmarks():
    fig = matplotlib.pyplot.figure(figsize=(8, 7))

    CONFIGS = [k for k in COLORS if "ocaml" not in k[0]]
    # CONFIGS = [k for k in COLORS if "Rupicola" in k[1]]
    # CONFIGS = [k for k in COLORS if "C" in k[1]]
    plot = add_plot(c_data, CONFIGS, ax=fig.add_subplot(111),
                    xlabel="Cycles per byte on 1MiB input (lower is better)")
    plot.legend(title="", loc='center right', bbox_to_anchor=(0.975, 0.425))

    fig.tight_layout()
    fig.savefig("benchmarks.pdf")

def ocaml_benchmarks():
    fig = matplotlib.pyplot.figure(figsize=(8, 7))

    CONFIGS = [
        ('GCC 11.1', 'Rupicola'),
        ('Clang 13.0', 'Rupicola'),

        ('GCC 11.1', 'C'),
        ('Clang 13.0', 'C'),

        ('ocamlopt 4.09', 'Coq/OCaml'),
    ]
    p1 = add_plot(ocaml_data, CONFIGS, selected_benchmarks=['ip'],
                  ax=fig.add_subplot(2, 1, 1), logmin=False,
                  xlabel="Cycles per byte on 1MiB input, linear scale (lower is better)")
    p2 = add_plot(ocaml_data, CONFIGS, selected_benchmarks=['ip'],
                  ax=fig.add_subplot(2, 1, 2), logmin=1,
                  xlabel="Cycles per byte on 1MiB input, log scale (lower is better)")
    p1.legend(title="", loc='upper right')
    p2.legend(title="", loc='upper right')

    fig.tight_layout()
    fig.savefig("benchmark-ocaml.pdf")

def main():
    seaborn.set_theme(font="Inconsolata", font_scale=1.5, style='ticks')
    matplotlib.rc('legend', frameon=False, labelspacing=0.2)
    c_benchmarks()
    ocaml_benchmarks()

if __name__ == '__main__':
    main()
