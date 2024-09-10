from matplotlib import pyplot as plt
import venn
import matplotlib.patches as patches
import pandas as pd

def run():
    with open("correct_result.csv", "r") as f:
        df = pd.read_csv(f)

    pyinder = set(df['Project'][df['Pyinder'] == 'O'])
    mypy = set(df['Project'][df['Mypy'] == 'O'])
    pyre = set(df['Project'][df['Pyre'] == 'O'])
    pytype = set(df['Project'][df['Pytype'] == 'O'])
    pyright = set(df['Project'][df['Pyright'] == 'O'])


    fig = plt.figure(figsize=(17, 4))
    labels = venn.get_labels([mypy, pyre, pytype, pyright], fill=['number'])
    fig1, ax = venn.venn4(labels, names=['Pyinder', 'Mypy', 'Pyre', 'Pyright'])
    ax.get_legend().remove()

    for t in ax.texts:
        t.set_fontsize(22)

    #labels = [attribute, classvar, dataflow]
    #venn3(labels, names=['Attribute', 'ClassVar', 'Dataflow'], figsize=(10,5))

    ax.axes.get_xaxis().set_visible(False)
    ax.axes.get_yaxis().set_visible(False)

    # plt.savefig("venn_main.pdf", format='pdf', bbox_inches='tight', pad_inches=0)

    sizes = [108, 86]
    labels = [f'Mypy\n({len(mypy)})', f'Pyre\n({len(pyre)})', f'Pytype\n({len(pytype)})', f'Pyright\n({len(pyright)})', f'Pyinder ({len(pyinder)})']
    colors = ['grey']

    diff_pyinder = pyinder - mypy - pyre - pytype - pyright

    circle_A = patches.Ellipse((0.5, 0.54), sizes[0]/100, sizes[1]/100, color=colors[0], alpha=0.2)
    plt.text(0.5, 0.85, f"{len(diff_pyinder)}", ha='center', va='center', color='black', fontsize=28)
    plt.gca().add_patch(circle_A)

    # Labeling
    plt.text(0.10, 0.74, labels[0], ha='center', va='center', color='black', fontsize=30)
    plt.text(0.30, 0.86, labels[1], ha='center', va='center', color='black', fontsize=30)
    plt.text(0.70, 0.86, labels[2], ha='center', va='center', color='black', fontsize=30)
    plt.text(0.90, 0.74, labels[3], ha='center', va='center', color='black', fontsize=30)

    plt.text(0.5, 0.99, labels[4], ha='center', va='center', color='black', fontsize=30)

    # labels = ['Mypy', 'Pyre', 'Pytype', 'Pyright', 'Pyinder']
    # plt.legend(labels=labels, loc='upper right', fontsize=16)

    plt.axis('off')
    plt.margins(0,0)
    plt.gca().xaxis.set_major_locator(plt.NullLocator())
    plt.gca().yaxis.set_major_locator(plt.NullLocator())
    # plt.tight_layout()
    plt.subplots_adjust(left=0, bottom=0)
    bbox = fig.bbox_inches.from_bounds(0, 1, 8.25, 7)
    plt.savefig("result_venn.pdf", format='pdf', bbox_inches=bbox, pad_inches=0)

if __name__ == "__main__":
    run()