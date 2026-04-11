import csv
import matplotlib.pyplot as plt
import sys
import os

def main():
    if not os.path.exists('data.csv'):
        print("data.csv not found. Did you run `lake exe tensor_sieve > data.csv`?")
        sys.exit(1)
        
    xs = []
    spacings = []
    
    with open('data.csv', 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row['jammed'] == '1':
                xs.append(int(row['x']))
                # ignore first spacing if it's 0 or just the value of first element
                if int(row['eigenvalue_spacing']) > 0:
                    spacings.append(int(row['eigenvalue_spacing']))

    if not xs:
        print("No jammed states found in data.")
        sys.exit(1)

    plt.figure(figsize=(12, 6))
    
    # Plot 1: Cumulative count of eigenvalues
    plt.subplot(1, 2, 1)
    plt.plot(xs, range(1, len(xs) + 1), marker='.', linestyle='none', color='red')
    plt.title('Trace Formula Convergence (Cumulative Zeros)')
    plt.xlabel('x (Energy Level)')
    plt.ylabel('N(x)')
    plt.grid(True)
    
    # Plot 2: Eigenvalue Spacing Distribution
    plt.subplot(1, 2, 2)
    plt.hist(spacings, bins=max(10, len(set(spacings))), alpha=0.7, color='blue', edgecolor='black')
    plt.title('Dynamic Eigenvalue Spacing')
    plt.xlabel('Spacing (\u0394x)')
    plt.ylabel('Frequency')
    plt.grid(True)
    
    plt.tight_layout()
    plt.savefig('spectrum_visualization.png')
    print("Saved visualization to spectrum_visualization.png")

if __name__ == '__main__':
    main()
